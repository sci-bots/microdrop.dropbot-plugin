"""
Copyright 2015-2017 Ryan Fobel and Christian Fobel

This file is part of dropbot_plugin.

dropbot_plugin is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

dropbot_plugin is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with dropbot_plugin.  If not, see <http://www.gnu.org/licenses/>.
"""
from collections import deque
from functools import wraps
import Queue
import datetime as dt
import gzip
import json
import logging
import pkg_resources
import re
import thread
import threading
import time
import types
import uuid
import warnings
import webbrowser

from dropbot import EVENT_ENABLE, EVENT_CHANNELS_UPDATED
from flatland import Integer, Float, Form, Boolean
from flatland.validation import ValueAtLeast, ValueAtMost
from matplotlib.backends.backend_gtkagg import (FigureCanvasGTKAgg as
                                                FigureCanvas)
from matplotlib.figure import Figure
from logging_helpers import _L  #: .. versionadded:: 2.24
from microdrop.app_context import get_app, get_hub_uri
from microdrop.gui.protocol_grid_controller import ProtocolGridController
from microdrop.plugin_helpers import (StepOptionsController, AppDataController)
from microdrop.plugin_manager import (IPlugin, IWaveformGenerator, Plugin,
                                      implements, PluginGlobals,
                                      ScheduleRequest, emit_signal,
                                      get_service_instance,
                                      get_service_instance_by_name)
from microdrop_utility.gui import yesno
from pygtkhelpers.gthreads import gtk_threadsafe
from pygtkhelpers.ui.dialogs import animation_dialog
from pygtkhelpers.utils import gsignal
from zmq_plugin.plugin import Plugin as ZmqPlugin
from zmq_plugin.schema import decode_content_data
import base_node_rpc as bnr
import dropbot as db
import dropbot.hardware_test
import dropbot.self_test
import gobject
import gtk
# XXX Use `json_tricks` rather than standard `json` to support serializing
# [Numpy arrays and scalars][1].
#
# [1]: http://json-tricks.readthedocs.io/en/latest/#numpy-arrays
import json_tricks
import numpy as np
import or_event
import pandas as pd
import path_helpers as ph
import semantic_version
import si_prefix as si
import tables
import zmq

from ._version import get_versions
from .noconflict import classmaker
__version__ = get_versions()['version']
del get_versions


# Reduce logging from `debounce` library.
for _ in ("debounce.%s" % i for i in ('setTimeout', 'shouldInvoke',
                                      'timerExpired', 'trailingEdge',
                                      'invokeFunc')):
    logging.getLogger(_).setLevel(logging.CRITICAL)

# Prevent warning about potential future changes to Numpy scalar encoding
# behaviour.
json_tricks.NumpyEncoder.SHOW_SCALAR_WARNING = False

# Ignore natural name warnings from PyTables [1].
#
# [1]: https://www.mail-archive.com/pytables-users@lists.sourceforge.net/msg01130.html
warnings.simplefilter('ignore', tables.NaturalNameWarning)

PluginGlobals.push_env('microdrop.managed')


class DmfZmqPlugin(ZmqPlugin):
    """
    API for adding/clearing droplet routes.
    """
    def __init__(self, parent, *args, **kwargs):
        self.parent = parent
        super(DmfZmqPlugin, self).__init__(*args, **kwargs)

    def check_sockets(self):
        """
        Check for messages on command and subscription sockets and process
        any messages accordingly.


        .. versionchanged:: 2.25.1
            Do not set actuated area according to electrode controller plugin
            messages.  Actuated area should be updated **_only once the DropBot
            reports the channels have been actuated_**.
        """
        try:
            msg_frames = self.command_socket.recv_multipart(zmq.NOBLOCK)
        except zmq.Again:
            pass
        else:
            self.on_command_recv(msg_frames)

        try:
            msg_frames = self.subscribe_socket.recv_multipart(zmq.NOBLOCK)
            source, target, msg_type, msg_json = msg_frames
            if all([source == 'microdrop.electrode_controller_plugin',
                    msg_type == 'execute_reply']):
                # The 'microdrop.electrode_controller_plugin' plugin maintains
                # the requested state of each electrode.
                msg = json.loads(msg_json)
                if msg['content']['command'] in ('set_electrode_state',
                                                 'set_electrode_states'):
                    data = decode_content_data(msg)
                    self.parent.update_channel_states(data['channel_states'])
                elif msg['content']['command'] == 'get_channel_states':
                    data = decode_content_data(msg)
                    self.parent.channel_states =\
                        self.parent.channel_states.iloc[0:0]
                    self.parent.update_channel_states(data['channel_states'])
            elif all([source == 'dmf_device_ui_plugin',
                      msg_type == 'execute_request']):
                msg = json.loads(msg_json)
                cmd = msg['content']['command']
                if cmd in ('measure_liquid_capacitance',
                           'measure_filler_capacitance'):
                    getattr(self.parent, 'on_%s' % cmd)()
            else:
                self.most_recent = msg_json
        except zmq.Again:
            pass
        except Exception:
            _L().error('Error processing message from subscription socket.',
                       exc_info=True)
        return True


def max_voltage(element, state):
    """Verify that the voltage is below a set maximum"""
    service = get_service_instance_by_name(ph.path(__file__).parent.name)

    if service.control_board and (element.value >
                                  service.control_board.max_waveform_voltage):
        return element.errors.append('Voltage exceeds the maximum value (%d '
                                     'V).' % service.control_board
                                     .max_waveform_voltage)
    else:
        return True


def check_frequency(element, state):
    """Verify that the frequency is within the valid range"""
    service = get_service_instance_by_name(ph.path(__file__).parent.name)

    if service.control_board and (element.value <
                                  service.control_board.min_waveform_frequency
                                  or element.value >
                                  service.control_board
                                  .max_waveform_frequency):
        return element.errors.append('Frequency is outside of the valid range '
                                     '(%.1f - %.1f Hz).' %
                                     (service.control_board
                                      .min_waveform_frequency,
                                      service.control_board
                                      .max_waveform_frequency))
    else:
        return True


def results_dialog(name, results, axis_count=1, parent=None):
    '''
    Given the name of a test and the corresponding results object, generate a
    GTK dialog displaying:

     - The formatted text output of the results
     - The corresponding axis plot(s) (if applicable).

    .. versionadded:: 0.14

    Parameters
    ----------
    name : str
        Test name (e.g., ``voltage``, ``channels``, etc.).
    results : dict
        Results from one or more :module:`dropbot.self_test` tests.
    axis_count : int, optional
        The number of figure axes required for plotting.
    parent : gtk.Window, optional
        The parent window of the dialog.

        This allows, for example, the dialog to be launched in front of the
        parent window and to disable controls on the parent window until the
        dialog is closed.
    '''
    # Resolve function for formatting results for specified test.
    format_func = getattr(db.self_test, 'format_%s_results' % name)
    try:
        # Resolve function for plotting results for specified test (if
        # available).
        plot_func = getattr(db.self_test, 'plot_%s_results' % name)
    except AttributeError:
        plot_func = None

    dialog = gtk.Dialog(parent=parent)
    title = re.sub(r'^test_', '', name).replace('_', ' ').title()
    dialog.set_title(title)
    dialog.props.destroy_with_parent = True
    dialog.props.window_position = gtk.WIN_POS_MOUSE

    label = gtk.Label()
    label.props.use_markup = True
    message = format_func(results[name])
    label.set_markup('<span face="monospace">{}</span>'.format(message))

    content_area = dialog.get_content_area()
    content_area.pack_start(label, fill=False, expand=False, padding=5)

    # Allocate minimum of 150 pixels height for report text.
    row_heights = [150]

    if plot_func is not None:
        # Plotting function is available.
        fig = Figure()
        canvas = FigureCanvas(fig)
        if axis_count > 1:
            # Plotting function plots to more than one axis.
            axes = [fig.add_subplot(axis_count, 1, i + 1)
                    for i in range(axis_count)]
            plot_func(results[name], axes=axes)
        else:
            # Plotting function plots to a single axis.
            axis = fig.add_subplot(111)
            plot_func(results[name], axis=axis)

        # Allocate minimum of 300 pixels height for report text.
        row_heights += axis_count * [300]
        fig.tight_layout()
        content_area.pack_start(canvas, fill=True, expand=True, padding=0)

    # Allocate minimum pixels height based on the number of axes.
    dialog.set_default_size(600, sum(row_heights))
    content_area.show_all()
    return dialog


def require_connection(log_level='error'):
    '''
    Decorator factory to require DropBot connection.

    Parameters
    ----------
    log_level : str
        Level to log message to if DropBot is not connect.

    Returns
    -------
    function
        Decorator to require DropBot connection.

    .. versionchanged:: 2.24
        Convert to decorator factory to add optional log-level customization.
    '''
    def _require_connection(func):
        @wraps(func)
        def _wrapped(self, *args, **kwargs):
            if not self.dropbot_connected.is_set():
                logger = _L()
                log_func = getattr(logger, log_level)
                log_func('DropBot is not connected.')
            else:
                return func(self, *args, **kwargs)
        return _wrapped
    return _require_connection


def error_ignore(on_error=None):
    '''
    Generate decorator for ignoring errors.

    Parameters
    ----------
    on_error : str or callable, optional
        Error message to log, or function to call if error occurs.

    Returns
    -------
    function
        Decorator function.
    '''
    def _decorator(func):
        @wraps(func)
        def _wrapped(*args, **kwargs):
            try:
                return func(*args, **kwargs)
            except Exception, exception:
                if isinstance(on_error, types.StringTypes):
                    print on_error
                elif callable(on_error):
                    on_error(exception, func, *args, **kwargs)
                else:
                    pass
        return _wrapped
    return _decorator


def require_test_board(func):
    '''
    Decorator to prompt user to insert DropBot test board.


    .. versionchanged:: 0.16

    .. versionchanged:: 2.25
        Add clickable hyperlink to DropBot Test Board documentation.
    '''
    @wraps(func)
    def _wrapped(*args, **kwargs):
        plugin_dir = ph.path(__file__).realpath().parent
        images_dir = plugin_dir.joinpath('images', 'insert_test_board')
        image_paths = sorted(images_dir.files('insert_test_board-*.jpg'))
        dialog = animation_dialog(image_paths, loop=True,
                                  buttons=gtk.BUTTONS_OK_CANCEL)
        dialog.props.text = ('<b>Please insert the DropBot test board</b>\n\n'
                             'For more info, see '
                             '<a href="https://github.com/sci-bots/dropbot-v3/wiki/DropBot-Test-Board#loading-dropbot-test-board">'
                             'the DropBot Test Board documentation</a>')

        def _on_link_clicked(label, uri):
            '''
            Callback to workaround the following error:

                GtkWarning: No application is registered as handling this file

            This is a known issue, e.g., https://bitbucket.org/tortoisehg/hgtk/issues/1656/link-in-about-box-doesnt-work#comment-312511
            '''
            webbrowser.open_new_tab(uri)
            return True
        # Use `activate-link` callback to manually handle action when hyperlink
        # is clicked/activated.
        dialog.label.connect("activate-link", _on_link_clicked)

        dialog.props.use_markup = True
        response = dialog.run()
        dialog.destroy()

        if response == gtk.RESPONSE_OK:
            return func(*args, **kwargs)
    return _wrapped


class DropBotPlugin(Plugin, gobject.GObject, StepOptionsController,
                    AppDataController):
    """
    This class is automatically registered with the PluginManager.

    .. versionchanged:: 0.19
        Inherit from ``gobject.GObject`` base class to add support for
        ``gsignal`` signals.

        Add ``gsignal`` signals for DropBot connection status and DMF chip
        status.
    """
    # Without the follow line, cannot inherit from both `Plugin` and
    # `gobject.GObject`.  See [here][1] for more details.
    #
    # [1]: http://code.activestate.com/recipes/204197-solving-the-metaclass-conflict/
    __metaclass__ = classmaker()

    #: ..versionadded:: 0.19
    gsignal('dropbot-connected', object)
    gsignal('dropbot-disconnected')
    gsignal('chip-inserted')
    gsignal('chip-removed')

    implements(IPlugin)
    implements(IWaveformGenerator)

    version = __version__
    plugin_name = str(ph.path(__file__).realpath().parent.name)

    @property
    def StepFields(self):
        """
        Expose StepFields as a property to avoid breaking code that accesses
        the StepFields member (vs through the get_step_form_class method).
        """
        return self.get_step_form_class()

    def __init__(self):
        '''
        .. versionchanged:: 0.19
            Add ``gsignal`` signals for DropBot connection status and DMF chip
            status.

            Set ``threading.Event`` when DropBot connection is established.

            Set ``threading.Event`` when DMF chip is inserted.

        .. versionchanged:: 2.22.4
            Register update of connection status when DropBot connects or
            disconnects.

        .. versionchanged:: 2.22.5
            Revert 2.22.4 changes since connection status is already updated
            when ``chip-removed`` or ``chip-inserted`` signals are emitted, and
            one of these signals is emitted whenever the DropBot either
            connects or disconnects.
        '''
        # Explicitly initialize GObject base class since it is not the first
        # base class listed.
        gobject.GObject.__init__(self)

        self.control_board = None
        self.name = self.plugin_name
        self.connection_status = "Not connected"
        self.current_frequency = None
        self.timeout_id = None
        self.channel_states = pd.Series()
        self.plugin = None
        self.plugin_timeout_id = None
        self.menu_items = []
        self.menu = None
        self.menu_item_root = None
        self.diagnostics_results_dir = '.dropbot-diagnostics'
        self.actuated_area = 0

        #: .. versionadded:: 2.24
        self.device_load_capacitance = 0

        #: .. versionadded:: 2.24
        self.actuation_voltage = 0

        #: .. versionadded:: 2.24
        self._step_capacitances = []

        #: .. versionadded:: 2.26
        self._state_applied = threading.Event()

        self._channel_states_received = threading.Event()

        #: .. versionadded:: 2.24
        self.device_time_sync = {}

        #: .. versionadded:: 2.25
        self.actuated_channels = []

        #: .. versionadded:: 2.24
        self.step_cancelled = threading.Event()
        #: .. versionadded:: 2.24
        self.capacitance_watch_thread = None
        #: .. versionadded:: 2.24
        self.capacitance_watch_finished = threading.Event()
        self.capacitance_watch_finished.set()
        #: .. versionadded:: 2.24
        self.capacitance_exceeded = threading.Event()

        self.chip_watch_thread = None
        self._chip_inserted = threading.Event()
        self._dropbot_connected = threading.Event()

        self.connect('chip-inserted', lambda *args:
                     self.chip_inserted.set())
        self.connect('chip-inserted', lambda *args:
                     self.update_connection_status())
        self.connect('chip-removed', lambda *args:
                     self.chip_inserted.clear())
        self.connect('chip-removed', lambda *args:
                     self.update_connection_status())

        def _on_dropbot_connected(*args):
            '''
            .. versionchanged:: 2.24
                Synchronize time between DropBot microseconds count and host
                UTC time.

                Update local actuation voltage with voltage sent in capacitance
                update events.

            .. versionchanged:: 2.25
                Update local list of actuated channels and associated actuated
                area from ``channels-updated`` device events.

            .. versionchanged:: 2.25.1
                Write the actuated channels list and actuated area to the debug
                log when the DropBot reports the actuated channels.

            .. versionchanged:: 2.26
                Set :attr:`_state_applied` event and log actuated channels/area
                to ``INFO`` level when ``channels-updated`` DropBot event is
                received.

            .. versionchanged:: 2.27
                Connect to the ``output_enabled`` and ``output_disabled``
                DropBot signals to update the chip insertion status.

                Configure :attr:`control_board.state.event_mask` to enable
                ``channels-updated`` events.
            '''
            # Set event indicating DropBot has been connected.
            self.dropbot_connected.set()

            OUTPUT_ENABLE_PIN = 22
            # Chip may have been inserted before connecting, so `chip-inserted`
            # event may have been missed.
            # Explicitly check if chip is inserted by reading **active low**
            # `OUTPUT_ENABLE_PIN`.
            if self.control_board.digital_read(OUTPUT_ENABLE_PIN):
                self.emit('chip-removed')
            else:
                self.emit('chip-inserted')

            # Connect to DropBot signals to monitor chip insertion status.
            self.control_board.signals.signal('output_enabled')\
                .connect(lambda message:
                         gtk_threadsafe(self.emit)('chip-inserted'),
                         weak=False)
            self.control_board.signals.signal('output_disabled')\
                .connect(lambda message:
                         gtk_threadsafe(self.emit)('chip-removed'),
                         weak=False)

            capacitance_update_status = {'time': time.time()}

            # Update cached device load capacitance each time the
            # `'capacitance-updated'` signal is emitted from the DropBot.
            def _on_capacitance_updated(message):
                if 'V_a' in message:
                    self.actuation_voltage = message['V_a']
                self.device_load_capacitance = message['new_value']
                now = time.time()
                if now - capacitance_update_status['time'] > .2:
                    self.on_device_capacitance_update(message['new_value'])
                    capacitance_update_status['time'] = now

            (self.control_board.signals.signal('capacitance-updated')
             .connect(_on_capacitance_updated, weak=False))
            # Request for the DropBot to measure the device load capacitance
            # every 100 ms.
            app_values = self.get_app_values()
            self.control_board.update_state(capacitance_update_interval_ms=
                                            app_values['c_update_ms'],
                                            event_mask=EVENT_CHANNELS_UPDATED |
                                            EVENT_ENABLE)
            _L().info('connected capacitance updated signal callback')

            self.device_time_sync = {'host': dt.datetime.utcnow(),
                                     'device_us':
                                     self.control_board.microseconds()}

            def _on_channels_updated(message):
                '''
                Message keys:
                 - ``"n"``: number of actuated channel
                 - ``"actuated"``: list of actuated channel identifiers.
                 - ``"start"``: ms counter before setting shift registers
                 - ``"end"``: ms counter after setting shift registers
                '''
                self.actuated_channels = message['actuated']
                if self.actuated_channels:
                    app = get_app()
                    actuated_electrodes = \
                        (app.dmf_device.actuated_electrodes(self
                                                            .actuated_channels)
                         .dropna())
                    actuated_areas = (app.dmf_device
                                      .electrode_areas.ix[actuated_electrodes
                                                          .values])
                    self.actuated_area = actuated_areas.sum()
                else:
                    self.actuated_area = 0
                _L().info('actuated electrodes: %s (%s mm^2)',
                          self.actuated_channels, self.actuated_area)
                self._state_applied.set()

            (self.control_board.signals.signal('channels-updated')
             .connect(_on_channels_updated, weak=False))
            _L().info('connected channels updated signal callback')

        self.connect('dropbot-connected', _on_dropbot_connected)

        def _on_dropbot_disconnected(*args):
            # Clear capacitance exceeded event since DropBot is not connected.
            self.capacitance_exceeded.clear()
            # Clear event indicating DropBot has been disconnected.
            self.dropbot_connected.clear()
            self.emit('chip-removed')

        self.connect('dropbot-disconnected', _on_dropbot_disconnected)

    @property
    def chip_inserted(self):
        '''
        Event set when a DMF chip is inserted into DropBot (and cleared when
        DMF chip is removed).

        .. versionadded:: 0.19
        '''
        return self._chip_inserted

    @property
    def dropbot_connected(self):
        '''
        Event set when DropBot is connected (and cleared when DropBot is
        disconnected).

        .. versionadded:: 0.19
        '''
        return self._dropbot_connected

    @gtk_threadsafe  # Execute in GTK main thread
    @error_ignore(lambda exception, func, self, test_name, *args:
                  _L().error('Error executing: "%s"', test_name,
                             exc_info=True))
    @require_connection()  # Display error dialog if DropBot is not connected.
    def execute_test(self, test_name, axis_count=1):
        '''
        Run single DropBot on-board self-diagnostic test.

        Record test results as JSON and display dialog to show text summary
        (and plot, where applicable).

        .. versionadded:: 0.14
        '''
        test_func = getattr(db.hardware_test, test_name)
        results = {test_name: test_func(self.control_board)}
        db.hardware_test.log_results(results, self.diagnostics_results_dir)
        format_func = getattr(db.self_test, 'format_%s_results' % test_name)
        message = format_func(results[test_name])
        map(_L().info, map(unicode.rstrip, unicode(message).splitlines()))

        app = get_app()
        parent = app.main_window_controller.view
        dialog = results_dialog(test_name, results, parent=parent,
                                axis_count=axis_count)
        dialog.run()
        dialog.destroy()

    @gtk_threadsafe  # Execute in GTK main thread
    @error_ignore(lambda *args:
                  _L().error('Error executing DropBot self tests.',
                             exc_info=True))
    @require_connection()  # Display error dialog if DropBot is not connected.
    @require_test_board  # Prompt user to insert DropBot test board
    def run_all_tests(self):
        '''
        Run all DropBot on-board self-diagnostic tests.

        Record test results as JSON and results summary as a Word document.


        .. versionadded:: 0.14

        .. versionchanged:: 0.16
            Prompt user to insert DropBot test board.

        .. versionchanged:: 2.28
            Generate a self-contained HTML report with JSON report results
            included in a ``<script id="results">...</script>`` tag.

        .. versionchanged:: 2.28
            Display a progress dialog while the test is running.
        '''
        gtk.gdk.threads_init()

        dialog = gtk.MessageDialog(buttons=gtk.BUTTONS_OK,
                                   flags=gtk.DIALOG_MODAL |
                                   gtk.DIALOG_DESTROY_WITH_PARENT)
        dialog.props.text = ('Running DropBot diagnostic self tests.\n\nThis '
                             'may take ~35 seconds to complete.  Please '
                             'wait...')
        dialog.set_title('DropBot self tests')
        dialog.props.destroy_with_parent = True
        dialog.props.window_position = gtk.WIN_POS_MOUSE
        # Disable `X` window close button.
        dialog.props.deletable = False
        content_area = dialog.get_content_area()
        progress = gtk.ProgressBar()
        content_area.pack_start(progress, fill=True, expand=True, padding=5)
        progress.props.can_focus = True
        progress.props.has_focus = True
        # Disable `OK` button until test has completed.
        dialog.get_action_area().props.sensitive = False
        content_area.show_all()

        # Need three active threads:
        #
        #  1. Main GTK thread calling this function, which will block when
        #     dialog is run/shown.
        #  2. DropBot self-test thread, which will block until test is
        #     complete.
        #  3. Progress update thread to refresh dialog progress bar while test
        #     is running and enable `OK` button once test has completed.

        # Set once DropBot self tests have completed.
        tests_completed = threading.Event()

        results = {}

        def _run_test():
            results_ = db.self_test.self_test(self.control_board)
            results.update(results_)
            tests_completed.set()

        def _update_progress():
            start = time.time()
            while not tests_completed.wait(1. / 5):
                # Update progress bar.
                gtk_threadsafe(progress.pulse)()
                gtk_threadsafe(progress.set_text)('Duration: %.0f s' %
                                                  (time.time() - start))

            # Test has completed.
            @gtk_threadsafe
            def _finish_dialog():
                progress.props.fraction = 1
                dialog.get_action_area().props.sensitive = True
                dialog.get_action_area().get_children()[0].props.has_focus = True
                progress.props.text = ('Completed after %.0f s. Click OK to '
                                       'open results in browser.' %
                                       (time.time() - start))
            _finish_dialog()

        for func_i in (_update_progress, _run_test):
            thread_i = threading.Thread(target=func_i)
            thread_i.daemon = True
            thread_i.start()

        # Launch dialog to show test activity and wait until test has
        # completed.
        dialog.run()
        dialog.destroy()

        # Test has completed, now:
        #
        #  1. Write raw JSON results to `.dropbot-diagnostics` directory in
        #     current working directory.
        #  2. Write HTML report to `.dropbot-diagnostics` directory in current
        #     working directory (with raw JSON results embedded in a
        #     `<script id="results" .../> tag).
        #  3. Launch HTML report in web browser.
        results_dir = ph.path(self.diagnostics_results_dir)
        results_dir.makedirs_p()

        # Create unique output filenames based on current timestamp.
        timestamp = dt.datetime.now().isoformat().replace(':', '_')
        json_path = results_dir.joinpath('results-%s.json' % timestamp)
        report_path = results_dir.joinpath('results-%s.html' % timestamp)

        # Write test results encoded as JSON.
        with json_path.open('w') as output:
            # XXX Use `json_tricks` rather than standard `json` to support
            # serializing [Numpy arrays and scalars][1].
            #
            # [1]: http://json-tricks.readthedocs.io/en/latest/#numpy-arrays
            output.write(json_tricks.dumps(results, indent=4))

        # Generate test result summary report as HTML document.
        db.self_test.generate_report(results, output_path=report_path,
                                     force=True)
        # Launch HTML report.
        report_path.launch()

    def create_ui(self):
        '''
        Create user interface elements (e.g., menu items).

        .. versionchanged:: 0.14
            Add "Run all on-board self-tests..." menu item.

            Add "On-board self-tests" menu.

        .. versionchanged:: 0.15
            Add "Help" menu item.

        .. versionchanged:: 0.16
            Prompt user to insert DropBot test board before running channels
            test.
        '''
        # Create head for DropBot on-board tests sub-menu.
        tests_menu_head = gtk.MenuItem('On-board self-_tests')

        # Create main DropBot menu.
        self.menu_items = [gtk.MenuItem('Run _all on-board self-tests...'),
                           gtk.MenuItem('_Help...'),
                           gtk.SeparatorMenuItem(), tests_menu_head]
        self.menu_items[0].connect('activate', lambda menu_item:
                                   self.run_all_tests())
        help_url = 'https://github.com/sci-bots/microdrop.dropbot-plugin/wiki/Quick-start-guide'
        self.menu_items[1].connect('activate', lambda menu_item:
                                   webbrowser.open_new_tab(help_url))
        app = get_app()
        self.menu = gtk.Menu()
        self.menu.show_all()
        self.menu_item_root = gtk.MenuItem('_DropBot')
        self.menu_item_root.set_submenu(self.menu)
        self.menu_item_root.show_all()
        for menu_item_i in self.menu_items:
            self.menu.append(menu_item_i)
            menu_item_i.show()

        # Add main DropBot menu to MicroDrop `Tools` menu.
        app.main_window_controller.menu_tools.append(self.menu_item_root)

        # Create DropBot on-board tests sub-menu.
        tests_menu = gtk.Menu()
        tests_menu_head.set_submenu(tests_menu)

        # List of on-board self-tests.
        tests = [{'test_name': 'test_voltage', 'title': 'Test high _voltage'},
                 {'test_name': 'test_on_board_feedback_calibration',
                  'title': 'On-board _feedback calibration'},
                 {'test_name': 'test_shorts', 'title': 'Detect _shorted '
                  'channels'},
                 {'test_name': 'test_channels', 'title': 'Scan test _board'}]

        # Add a menu item for each test to on-board tests sub-menu.
        for i, test_i in enumerate(tests):
            axis_count_i = 2 if test_i['test_name'] == 'test_channels' else 1
            menu_item_i = gtk.MenuItem(test_i['title'])

            def _exec_test(menu_item, test_name, axis_count):
                self.execute_test(test_name, axis_count)

            if test_i['test_name'] == 'test_channels':
                # Test board is required for `test_channels` test.
                _exec_test = require_test_board(_exec_test)

            menu_item_i.connect('activate', _exec_test, test_i['test_name'],
                                axis_count_i)
            menu_item_i.show()
            tests_menu.append(menu_item_i)

    @property
    def AppFields(self):
        '''
        .. versionchanged:: 0.22.2
            Remove serial port, which is no longer used as of version 0.22.

        .. versionchanged:: 2.26
            Add capacitance update interval, i.e., ``c_update_ms``, specifying
            the interval to request the DropBot to send capacitance measurement
            updates.
        '''
        return Form.of(
            Float.named('default_duration').using(default=1000, optional=True),
            Float.named('default_voltage').using(default=80, optional=True),
            Float.named('default_frequency').using(default=10e3,
                                                   optional=True),
            Boolean.named('Auto-run diagnostic tests').using(default=True,
                                                             optional=True),
            #: .. versionadded:: 0.18
            Float.named('c_liquid').using(default=0, optional=True,
                                          properties={'show_in_gui': False}),
            #: .. versionadded:: 0.18
            Float.named('c_filler').using(default=0, optional=True,
                                          properties={'show_in_gui': False}),
            #: .. versionadded:: 2.26
            Integer.named('c_update_ms').using(default=10, optional=True,
                                               properties={'show_in_gui':
                                                           True}))

    def get_step_form_class(self):
        """
        Override to set default values based on their corresponding app options.


        .. versionchanged:: 2.25.2
            Deprecate the ``max_repeats`` step option since it is no longer
            used.
        """
        app_values = self.get_app_values()
        return Form.of(Integer.named('duration')
                       .using(default=app_values['default_duration'],
                              optional=True,
                              validators=[ValueAtLeast(minimum=0)]),
                       Float.named('voltage')
                       .using(default=app_values['default_voltage'],
                              optional=True,
                              validators=[ValueAtLeast(minimum=0),
                                          max_voltage]),
                       Float.named('frequency')
                       .using(default=app_values['default_frequency'],
                              optional=True,
                              validators=[ValueAtLeast(minimum=0),
                                          check_frequency]),
                       #: .. versionadded:: 0.18
                       Float.named('volume_threshold')
                       .using(default=0,
                              optional=True,
                              validators=[ValueAtLeast(minimum=0),
                                          ValueAtMost(maximum=1.0)]))

    def update_channel_states(self, channel_states):
        _L().info('update_channel_states')
        # Update locally cached channel states with new modified states.
        try:
            self.channel_states = channel_states.combine_first(self
                                                               .channel_states)
        except ValueError:
            logging.info('channel_states: %s', channel_states)
            logging.info('self.channel_states: %s', self.channel_states)
            logging.info('', exc_info=True)
        else:
            self._channel_states_received.channel_states = \
                self.channel_states.copy()
            if self._channel_states_received.is_set():
                self.on_step_run()
            else:
                self._channel_states_received.set()

    def cleanup_plugin(self):
        '''
        .. versionchanged:: 2.25
            Kill any currently running step.
        '''
        self._kill_running_step()
        if self.plugin_timeout_id is not None:
            gobject.source_remove(self.plugin_timeout_id)
        if self.plugin is not None:
            self.plugin = None
        if self.dropbot_connected.is_set():
            self.control_board.hv_output_enabled = False
            self.control_board.terminate()
            self.control_board = None
            gobject.idle_add(self.emit, 'dropbot-disconnected')

    def on_plugin_enable(self):
        '''
        .. versionchanged:: 0.19
            Launch background thread to monitor for DMF chip status events from
            DropBot serial stream.

        .. versionchanged:: 2.22.4
            Initialize connection status before attempting to connect to
            DropBot.  This allows, for example, menu items requiring a DropBot
            to default to non-sensitive.
        '''
        super(DropBotPlugin, self).on_plugin_enable()
        if not self.menu_items:
            # Schedule initialization of menu user interface.  Calling
            # `create_ui()` directly is not thread-safe, since it includes GTK
            # code.
            gobject.idle_add(self.create_ui)

        self.cleanup_plugin()
        self.update_connection_status()

        # Initialize 0MQ hub plugin and subscribe to hub messages.
        self.plugin = DmfZmqPlugin(self, self.name, get_hub_uri(),
                                   subscribe_options={zmq.SUBSCRIBE: ''})
        # Initialize sockets.
        self.plugin.reset()

        # Periodically process outstanding message received on plugin sockets.
        self.plugin_timeout_id = gtk.timeout_add(10, self.plugin.check_sockets)

        self.connect_dropbot()
        if get_app().protocol:
            self.on_step_run()
            self._update_protocol_grid()

    def on_plugin_disable(self):
        self.cleanup_plugin()
        if get_app().protocol:
            self.on_step_run()
            self._update_protocol_grid()

    def on_app_exit(self):
        """
        Handler called just before the Microdrop application exits.

        .. versionchanged:: 0.19
            Emit ``dropbot-disconnected`` ``gsignal`` after closing DropBot
            connection.
        """
        self.cleanup_plugin()
        try:
            # TODO Is this required?  This code is already run in
            # `cleanup_plugin()`.
            self.control_board.hv_output_enabled = False
            self.control_board.terminate()
            self.control_board = None
            gobject.idle_add(self.emit, 'dropbot-disconnected')
        except Exception:
            # ignore any exceptions (e.g., if the board is not connected)
            pass

    def on_protocol_swapped(self, old_protocol, protocol):
        self._update_protocol_grid()

    def _update_protocol_grid(self):
        pgc = get_service_instance(ProtocolGridController, env='microdrop')
        if pgc.enabled_fields:
            pgc.update_grid()

    def on_app_options_changed(self, plugin_name):
        '''
        .. versionchanged:: 0.22.2
            Remove check for serial port, which is no longer used as of version
            0.22.

        .. versionchanged:: 2.26
            Apply specified capacitance update interval to DropBot (if
            connected).
        '''
        app = get_app()
        if plugin_name == self.name:
            self._update_protocol_grid()
        elif plugin_name == app.name:
            # Turn off all electrodes if we're not in realtime mode and not
            # running a protocol.
            if self.dropbot_connected.is_set():
                app_values = self.get_app_values()
                self.control_board.update_state(capacitance_update_interval_ms=
                                                app_values['c_update_ms'])
                if not app.realtime_mode and not app.running:
                    _L().info('Turning off all electrodes.')
                    self.control_board.hv_output_enabled = False

    def connect_dropbot(self):
        """
        Try to connect to the DropBot control board.

        If multiple DropBots are available, automatically select DropBot with
        highest version, with ties going to the lowest port name (i.e.,
        ``COM1`` before ``COM2``).

        .. versionchanged:: 0.19
            Rename method to ``connect_dropbot`` to avoid a name collision with
            the ``gobject.GObject.connect`` method.

            Emit ``dropbot-connected`` ``gsignal`` after establishing DropBot
            connection.

            Emit ``dropbot-disconnected`` ``gsignal`` after closing DropBot
            connection.
        .. versionchanged:: 0.22
            Use new :mod:`base_node_rpc` serial device connection code to
            connect to DropBot.

            If multiple DropBots are detected, automatically connect to DropBot
            with highest version with ties going to the first serial port
            (i.e., ``COM1`` before ``COM2``).

            Offer to *flash firmware* if no DropBot is detected, or if a
            DropBot is found with a firmware version that does not match the
            installed driver version.
        """
        if self.control_board:
            self.control_board.terminate()
            self.control_board = None
            gobject.idle_add(self.emit, 'dropbot-disconnected')
        self.current_frequency = None

        def _attempt_connect(**kwargs):
            '''
            .. versionadded:: 0.22

            Attempt connection to DropBot.


            .. versionchanged:: 2.27
                Ignore mismatch between DropBot driver and firmware versions as
                long as base minor versions are equal, i.e., assume API is
                backwards compatible.
            '''
            try:
                self.control_board = db.SerialProxy(**kwargs)
                # Emit signal to notify that DropBot connection was
                # established.
                gobject.idle_add(self.emit, 'dropbot-connected',
                                 self.control_board)
            except bnr.proxy.DeviceVersionMismatch as exception:
                # DropBot device software version does not match host software
                # version.

                # Check if base minor versions match (e.g., `1.53rc0` and
                # `1.53rc1`; `1.53.0` and `1.53.1`).
                try:
                    versions = [semantic_version.Version(pkg_resources
                                                         .parse_version(v)
                                                         .base_version,
                                                         partial=True)
                                for v in (exception.device_version,
                                          db.__version__)]
                except Exception as e:
                    versions = []
                    gobject.idle_add(_L().warning, str(e))

                if len(set([(v.major, v.minor) for v in versions])) == 1:
                    # Base minor versions are *equal*.  Assume API is backwards
                    # compatible and attempt to connect.
                    _attempt_connect(ignore=[bnr.proxy.DeviceVersionMismatch])
                else:
                    _offer_to_flash('\n'.join([str(exception), '', 'Flash '
                                               'firmware version %s?' %
                                               exception.device_version]))
            except bnr.proxy.DeviceNotFound as exception:
                # Cases:
                #
                #  - Device `...` does not match expected name `dropbot`.
                #  - No named devices found.
                #  - No dropbot device found.
                #  - No devices found with matching name.
                #
                # Assume a DropBot is actually connected and offer to flash the
                # latest firmware.
                messages = ['\n'.join(['DropBot could not be detected.' '',
                                       'Is a DropBot plugged in?']),
                            'Flash firmware version %s?' % db.__version__]
                _offer_to_flash(messages)
            except bnr.proxy.MultipleDevicesFound:
                # Multiple DropBot devices were found.
                # Get list of available devices.
                df_comports = bnr.available_devices(timeout=.1)
                # Automatically select DropBot with highest version, with ties
                # going to the lowest port name (i.e., `COM1` before `COM2`).
                df_comports = df_comports.loc[df_comports.device_name ==
                                              'dropbot'].copy()
                df_comports.reset_index(inplace=True)
                df_comports.sort_values(['device_version', 'port'],
                                        ascending=[False, True], inplace=True)
                df_comports.set_index('port', inplace=True)
                port = df_comports.index[0]
                # Attempt to connect to automatically selected port.
                _attempt_connect(port=port,
                                 ignore=[bnr.proxy.MultipleDevicesFound])
            except Exception as exception:
                gobject.idle_add(_L().error, str(exception))

        @gtk_threadsafe
        def _offer_to_flash(message):
            '''
            .. versionadded:: 0.22

            Launch user prompts in GTK main thread to offer to flash new
            DropBot firmware.

            Parameters
            ----------
            message : str or list
                One or more messages to ask the user.

                Firmware is only flashed if user answers **Yes** to all
                questions.
            '''
            if isinstance(message, types.StringTypes):
                message = [message]

            for message_i in message:
                response = yesno(message_i)
                if response != gtk.RESPONSE_YES:
                    # User answered no, so do not flash firmware.
                    break
            else:
                # User answered yes to all questions.
                _L().debug('Upload DropBot firmware version %s',
                           db.__version__)
                db.bin.upload.upload()
                time.sleep(0.5)
                _attempt_connect()

        _attempt_connect()

    def data_dir(self):
        '''
        .. versionadded:: 0.18
        '''
        app = get_app()
        data_dir = app.experiment_log.get_log_path().joinpath(self.name)
        if not data_dir.isdir():
            data_dir.makedirs_p()
        return data_dir

    def check_device_name_and_version(self):
        '''
        .. versionchanged:: 0.22
        '''
        raise DeprecationWarning('check_device_name_and_version is '
                                 'deprecated.')

    def on_flash_firmware(self, widget=None, data=None):
        '''
        .. versionchanged:: 0.22
        '''
        raise DeprecationWarning('on_flash_firmware is deprecated.  Firmware '
                                 'flashing is now handled in the '
                                 '`connect_dropbot` method')

    def update_connection_status(self):
        '''
        Update connection status message and corresponding UI label.

        .. versionchanged:: 0.14
            Schedule update of control board status label in main GTK thread.

        .. versionchanged:: 0.18
            Toggle sensitivity of DropBot control board menu items based on
            control board connection status.

        .. versionchanged:: 0.19
            Always keep ``Help`` menu item sensitive, regardless of DropBot
            connection status.

            Indicate if chip is inserted in UI status label.
        '''
        self.connection_status = "Not connected"
        app = get_app()
        if self.dropbot_connected.is_set():
            properties = self.control_board.properties
            version = self.control_board.hardware_version
            n_channels = self.control_board.number_of_channels
            id = self.control_board.id
            uuid = self.control_board.uuid
            self.connection_status = ('%s v%s (Firmware: %s, id: %s, uuid: '
                                      '%s)\n' '%d channels%s' %
                                      (properties['display_name'], version,
                                       properties['software_version'], id,
                                       str(uuid)[:8], n_channels,
                                       '' if not self.chip_inserted.is_set()
                                       else ' [chip inserted]'))

        @gtk_threadsafe
        def _update_ui_connected_status():
            # Enable/disable control board menu items based on the connection
            # status of the control board.
            for menu_item_i in self.menu_items:
                if 'Help' not in menu_item_i.props.label:
                    menu_item_i.set_sensitive(self.dropbot_connected.is_set())

            app.main_window_controller.label_control_board_status\
                .set_text(self.connection_status)
        _update_ui_connected_status()

    @require_connection(log_level='info')  # Log if DropBot is not connected.
    def measure_capacitance(self):
        '''
        Measure the capacitance of all actuated electrodes on the device
        and send an 'on_device_capacitance_update' signal to update to
        any listeners.

        .. versionadded:: 0.18
        '''
        c = self.control_board.measure_capacitance()
        v = self.control_board.measure_voltage()
        # send a signal to update the gui
        emit_signal('on_device_capacitance_update', c)
        return dict(capacitance=c, voltage=v)

    def on_device_capacitance_update(self, capacitance):
        '''
        .. versionadded:: 0.18

        .. versionchanged:: 0.19
            Simplify control board status label update.

        .. versionchanged:: 0.22
            Use :func:`numpy.where` instead of :func:`mlab.find` since
            :mod:`numpy` is already a dependency.

        .. versionchanged:: 2.24
            Change method signature to accept capacitance as only argument.

            Deprecate CSV logging on capacitance update.  Multiple capacitance
            measurements are instead logged at the end of each step to a
            GZip-compressed CSV file.

        Parameters
        ----------
        capacitance : float
            Device load capacitance value.
        '''
        # Use cached actuation voltage measurement taken ~100 ms after voltage
        # was set.
        voltage = self.actuation_voltage

        app = get_app()
        app_values = self.get_app_values()
        c_liquid = app_values['c_liquid']

        label = 'Voltage: {}V, Capacitance: {}F'.format(*map(si.si_format,
                                                             (voltage,
                                                              capacitance)))

        # add normalized force to the label if we've calibrated the device
        if c_liquid > 0:
            # TODO: calculate force including filler media
            label += (u'\nForce: {}N/mm (c<sub>device</sub>='
                      u'{}F/mm<sup>2</sup>)'
                      .format(*map(si.si_format, (1e3 * 0.5 * c_liquid *
                                                  voltage ** 2, c_liquid))))

        # Schedule update of control board status label in main GTK thread.
        gobject.idle_add(app.main_window_controller.label_control_board_status
                         .set_markup, ', '.join([self.connection_status,
                                                 label]))

    def _calibrate_device_capacitance(self, name):
        '''
        .. versionadded:: 0.18
        '''
        if not self.dropbot_connected.is_set():
            _L().error('DropBot is not connected.')
        elif self.actuated_area == 0:
            _L().error('At least one electrode must be actuated to perform '
                       'calibration.')
        else:
            max_channels = self.control_board.number_of_channels
            # All channels should default to off.
            channel_states = np.zeros(max_channels, dtype=int)
            # Set the state of any channels that have been set explicitly.
            channel_states[self.channel_states.index
                           .values.tolist()] = self.channel_states

            # enable high voltage
            if not self.control_board.hv_output_enabled:
                # XXX Only set if necessary, since there is a ~200 ms delay.
                self.control_board.hv_output_enabled = True

            # set the voltage and frequency specified for the current step
            options = self.get_step_options()
            emit_signal("set_frequency",
                        options['frequency'],
                        interface=IWaveformGenerator)
            emit_signal("set_voltage", options['voltage'],
                        interface=IWaveformGenerator)

            # perform the capacitance measurement
            self.control_board.set_state_of_channels(channel_states)
            c = self.control_board.measure_capacitance()
            _L().info("on_measure_%s_capacitance: {}F/%.1f mm^2 = {}F/mm^2",
                      name, si.si_format(c), self.actuated_area,
                      si.si_format(c / self.actuated_area))
            app_values = {}
            app_values['c_%s' % name] = c / self.actuated_area
            self.set_app_values(app_values)

            # send a signal to update the gui
            emit_signal('on_device_capacitance_update', c)

            # Turn off all electrodes and disable high voltage if we're
            # not in realtime mode.
            if not get_app().realtime_mode:
                self.control_board.hv_output_enabled = False
                self.control_board.set_state_of_channels(
                    np.zeros(max_channels, dtype=int))

    def on_measure_liquid_capacitance(self):
        '''
        .. versionadded:: 0.18
        '''
        self._calibrate_device_capacitance('liquid')

    def on_measure_filler_capacitance(self):
        '''
        .. versionadded:: 0.18
        '''
        self._calibrate_device_capacitance('filler')

    @require_connection(log_level='info')  # Log if DropBot is not connected.
    def _apply_state(self):
        '''
        .. versionchanged:: 2.25
            Use :meth:`_on_step_capacitance_updated` callback to add current
            list of actuated channels and associated actuated area to
            capacitance update message.

        .. versionchanged:: 2.26
            Clear :attr:`_state_applied` event since new state is being
            applied.
        '''
        self.capacitance_exceeded.clear()
        self._state_applied.clear()
        options = self.get_step_options()
        max_channels = self.control_board.number_of_channels
        # All channels should default to off.
        channel_states = np.zeros(max_channels, dtype=int)
        # Set the state of any channels that have been set explicitly.
        channel_states[self.channel_states.index
                       .values.tolist()] = self.channel_states

        emit_signal("set_frequency",
                    options['frequency'],
                    interface=IWaveformGenerator)
        emit_signal("set_voltage", options['voltage'],
                    interface=IWaveformGenerator)
        if not self.control_board.hv_output_enabled:
            # XXX Only set if necessary, since there is a ~200 ms delay.
            self.control_board.hv_output_enabled = True

        logger = _L()  # use logger with method context
        self.control_board.set_state_of_channels(channel_states)
        if logging.getLogger().isEnabledFor(logging.DEBUG):
            logger.debug('Actuate channels: %s', np.where(channel_states)[0])
            logger.debug('DropBot state:')
            map(logger.debug, str(self.control_board.state).splitlines())

        # Connect to `capacitance-updated` signal to record capacitance
        # values measured during the step.
        (self.control_board.signals.signal('capacitance-updated')
         .connect(self._on_step_capacitance_updated, weak=False))
        logger.info('connected capacitance updated signal callback')

    def on_step_run(self):
        '''
        Handler called whenever a step is executed.

        Plugins that handle this signal must emit the on_step_complete
        signal once they have completed the step. The protocol controller
        will wait until all plugins have completed the current step before
        proceeding.

        .. versionchanged:: 0.14
            Schedule update of control board status label in main GTK thread.

        .. versionchanged:: 0.18
            Do not update control board status label.

            Instead, status is updated when capacitance is measured a) after
            actuation in real-time mode, or b) after step duration is complete
            when protocol is running.

        .. versionchanged:: 2.24
            Use a thread and corresponding :class:`threading.Event` instances
            to watch for the threshold capacitance (if set) to be reached.  If
            the threshold is not met by the specified duration of the step,
            time out and stop the protocol.

        .. versionchanged:: 2.25.2
            Connect to ``capacitance-updated`` event (in addition to
            ``capacitance-exceeded`` event) to check against target
            capacitance.

        .. versionchanged:: 2.26
            Wait for :attr:`_state_applied` event to ensure pending electrode
            actuations have completed before computing target capacitance based

            Require **5 consecutive** capacitance updates above the target
            threshold to trigger step completion.  This increases confidence
            that the target capacitance has actually been met.

        .. versionchanged:: 2.27
            Wait in separate thread for channel states to be applied. This
            allows GTK events and step handling of other plugins to execute
            concurrently.
        '''
        self._kill_running_step()
        self.step_cancelled.clear()
        self._step_uuid = uuid.uuid5(uuid.uuid1(), 'dropbot_plugin')

        def _wait_for_channel_states():
            event = or_event.OrEvent(self.step_cancelled,
                                     self._channel_states_received)
            # Wait for channel states to be received.
            event.wait()

            if self.step_cancelled.is_set():
                self.complete_step()
            else:
                # Channel states have been received.  Execute step.
                gtk_threadsafe(self._execute_step)()

        thread = threading.Thread(target=_wait_for_channel_states)
        thread.daemon = True
        thread.start()

    @gtk_threadsafe
    def _execute_step(self):
        '''
        Execute step only after channel states have been received.

        .. versionadded:: 2.27
        '''
        def _delay_completion(duration_s):
            '''
            Delay until either a) specified duration has passed; or b) step has
            been cancelled.
            '''
            step_uuid = self._step_uuid

            def _wait_for_cancelled():
                if self.step_cancelled.wait(duration_s):
                    self.step_cancelled.clear()
                    # Step was cancelled.
                    _L().info('Step was cancelled.')
                    self._kill_running_step()
                elif step_uuid == self._step_uuid:
                    _L().info('Complete step after %ss', si.si_format(duration_s))
                    self.complete_step()

            thread = threading.Thread(target=_wait_for_cancelled)
            thread.daemon = True
            thread.start()

        # Clear step cancelled signal.
        self.step_cancelled.clear()
        app = get_app()

        if app.realtime_mode or app.running:
            self._apply_state()

        if app.realtime_mode and not app.running:
            # Measure the voltage and capacitance and update the GUI.
            self.measure_capacitance()

        if not app.running:
            # Protocol is not running so do not apply capacitance threshold or
            # duration.
            self.complete_step()
        else:
            options = self.get_step_options()
            app_values = self.get_app_values()

            # Criteria that must be met to set target capacitance.
            threshold_criteria = [options['volume_threshold'] > 0,
                                  self.actuated_area > 0,
                                  app_values['c_liquid'] > 0]

            if not self.dropbot_connected.is_set():
                if options['volume_threshold'] > 0:
                    # Volume threshold is set.  Treat `duration` as maximum
                    # duration and continue immediately.
                    self.complete_step()
                else:
                    # DropBot is not connected.  Delay for specified duration.
                    _delay_completion(options['duration'] * 1e-3)
            elif all(threshold_criteria):
                # A volume threshold has been set for this step.

                # Calculate target capacitance based on actuated area.
                #
                # Note: `app_values['c_liquid']` represents a *specific
                # capacitance*, i.e., has units of $F/mm^2$.
                duration_s = options['duration'] * 1e-3
                if self._state_applied.wait(duration_s):
                    target_capacitance = (options['volume_threshold'] *
                                        self.actuated_area *
                                        app_values['c_liquid'])
                    _L().info('target capacitance: %sF (actuated area: %s mm^2'
                              ', actuated channels: %s)',
                              si.si_format(target_capacitance),
                              self.actuated_area, self.actuated_channels)
                else:
                    # Timed out waiting for capacitance.
                    # XXX Include the value of the capacitance that *was*
                    # reached in the log message.
                    _L().warn('Timed out waiting for DropBot to apply '
                              'requested settings.')
                    self.complete_step('Fail')
                    return

                def _wait_for_target_capacitance():
                    _L().debug('thread started: %s', thread.get_ident())
                    self.capacitance_watch_finished.clear()
                    event = or_event.OrEvent(self.step_cancelled,
                                             self.capacitance_exceeded)
                    capacitance_window = deque()
                    N = 5

                    # Connect capacitance updates callback to check against
                    # target capacitance.
                    def _check_threshold(message):
                        capacitance_window.appendleft(message['new_value'])
                        if len(capacitance_window) > N:
                            capacitance_window.pop()
                        self.capacitance_exceeded.window = \
                            list(capacitance_window)
                        stable_capacitance = min(self.capacitance_exceeded
                                                 .window)

                        if all([len(capacitance_window) >= N,
                                stable_capacitance > target_capacitance]):
                            message['new_value'] = stable_capacitance
                            self.capacitance_exceeded.set()
                            self.capacitance_exceeded.result = message

                    (self.control_board.signals.signal('capacitance-updated')
                     .connect(_check_threshold, weak=False))

                    if event.wait(duration_s):
                        if self.capacitance_exceeded.is_set():
                            self.capacitance_exceeded.clear()
                            capacitance = (self.capacitance_exceeded
                                           .result['new_value'])
                            # Step was completed successfully within specified
                            # duration.
                            _L().info('Target capacitance was reached: %sF > '
                                      '%sF (window: %s)',
                                      *(map(si.si_format,
                                            (capacitance, target_capacitance))
                                        + [map(si.si_format,
                                               self.capacitance_exceeded
                                               .window)]))
                            gtk_threadsafe(self.complete_step)()
                        elif self.step_cancelled.is_set():
                            # Step was cancelled.
                            _L().info('Step was cancelled.')
                    else:
                        # Timed out waiting for capacitance.
                        # XXX Include the value of the capacitance that *was*
                        # reached in the log message.
                        _L().warn('Timed out.  Capacitance %sF did not reach '
                                  'target of %sF after %ss.',
                                  *map(si.si_format,
                                       (min(capacitance_window),
                                        target_capacitance, duration_s)))
                        gtk_threadsafe(self.complete_step)('Fail')

                    # Disconnect capacitance updates callback.
                    (self.control_board.signals.signal('capacitance-updated')
                     .disconnect(_check_threshold))

                    # Signal that capacitance watch thread has completed.
                    self.capacitance_watch_finished.set()
                    _L().debug('thread finished: %s', thread.get_ident())

                # Start thread to wait for target capacitance to be met.
                self.capacitance_watch_thread = \
                    threading.Thread(target=_wait_for_target_capacitance)
                # Stop when main thread exits.
                self.capacitance_watch_thread.daemon = True
                self.capacitance_watch_thread.start()
            else:
                _L().info('actuated area: %s mm^2', self.actuated_area)
                _delay_completion(options['duration'] * 1e-3)

    @require_connection(log_level='info')  # Log if DropBot is not connected.
    def log_capacitance_updates(self, capacitance_updates):
        '''
        .. versionadded:: 2.24

        Append the specified capacitance update messages to a GZip-compressed
        CSV table in the current experiment log directory.

        Parameters
        ----------
        capacitance_updates : list
            List of ``"capacitance-updated"`` event messages.


        .. versionchanged:: 2.25
            Use actuated channels lists and actuated areas from capacitance
            updates.

        .. versionchanged:: 2.26
            Remove ``sampling_rate_hz`` column.  Move ``capacitance`` column to
            index 1 (adjacent to ``timestamp_utc`` column).
        '''
        app = get_app()

        # Append data to CSV file.
        csv_output_path = self.data_dir().joinpath('data.csv.gz')
        # Only include header if the file does not exist or is empty.
        include_header = not (csv_output_path.isfile() and
                              (csv_output_path.size > 0))

        df = (pd.DataFrame(capacitance_updates).drop('event', axis=1)
              .rename(columns={'new_value': 'capacitance'}))
        # Compute UTC timestamp based on host time synced with DropBot
        # microseconds count.
        df.insert(0, 'timestamp_utc', self.device_time_sync['host'] +
                  ((df['end'] - self.device_time_sync['device_us']) *
                   1e-6).map(lambda x: dt.timedelta(seconds=x)))
        df.insert(2, 'step', app.protocol.current_step_number + 1)
        # Drop `start` and `end` columns since relevant time information is
        # stored in `timestamp_utc`.
        df.drop(['start', 'end'], axis=1, inplace=True)

        # Use `compresslevel=1` to prioritize compression speed while still
        # significantly reducing the output file size compared to no
        # compression.
        #
        # See [here][1] for some supporting motivation.
        #
        # [1]: https://github.com/gruntjs/grunt-contrib-compress/issues/116#issuecomment-70883022
        with gzip.open(csv_output_path, 'a', compresslevel=1) as output:
            df.to_csv(output, index=False, header=include_header)

    def _on_step_capacitance_updated(self, message):
        '''
        .. versionadded:: 2.25


        Callback for ``capacitance-updated`` DropBot device events (only called
        when step is running).

        Add current list of actuated channels and associated actuated electrode
        area to capacitance update message and add message to list of updates
        for the currently running step.
        '''
        message['actuated_channels'] = self.actuated_channels
        message['actuated_area'] = self.actuated_area
        self._step_capacitances.append(message)

    def complete_step(self, return_value=None):
        self._channel_states_received.clear()
        self.timeout_id = None
        app = get_app()
        if app.running or app.realtime_mode:
            if self.dropbot_connected.is_set():
                # Disconnect from `capacitance-updated` signal to stop
                # recording capacitance values now that the step has finished.
                (self.control_board.signals.signal('capacitance-updated')
                 .disconnect(self._on_step_capacitance_updated))
            if self._step_capacitances:
                self.log_capacitance_updates(self._step_capacitances)
                _L().info('logged %d capacitance readings.',
                          len(self._step_capacitances))
                self._step_capacitances = []
            emit_signal('on_step_complete', [self.name, return_value])

    def _kill_running_step(self):
        '''
        .. versionchanged:: 2.25
            Stop recording capacitance updates.

        .. versionchanged:: 2.26
            Clear :attr:`_state_applied` event.

        .. versionchanged:: 2.27
            Clear :attr:`_channel_states_received` event.
        '''
        self._step_thread = None
        self._state_applied.clear()
        if self.timeout_id:
            _L().debug('remove timeout_id=%d', self.timeout_id)
            gobject.source_remove(self.timeout_id)
        # Signal that step has been cancelled.
        self.step_cancelled.set()
        # Wait for capacitance threshold watching thread to stop.
        self.capacitance_watch_finished.wait()
        if self.dropbot_connected.is_set():
            # Stop recording capacitance updates.
            (self.control_board.signals.signal('capacitance-updated')
             .disconnect(self._step_capacitances.append))

    def on_protocol_run(self):
        """
        Handler called when a protocol starts running.
        """
        app = get_app()
        if not self.dropbot_connected.is_set():
            _L().warning("Warning: no control board connected.")
        elif (self.control_board.number_of_channels <=
              app.dmf_device.max_channel()):
            _L().warning("Warning: currently connected board does not have "
                         "enough channels for this protocol.")

    def on_protocol_pause(self):
        """
        Handler called when a protocol is paused.
        """
        app = get_app()
        self._kill_running_step()
        if self.dropbot_connected.is_set() and not app.realtime_mode:
            # Turn off all electrodes
            _L().debug('Turning off all electrodes.')
            self.control_board.hv_output_enabled = False

    def on_experiment_log_selection_changed(self, data):
        """
        Handler called whenever the experiment log selection changes.

        Parameters:
            data : dictionary of experiment log data for the selected steps
        """
        pass

    @require_connection(log_level='info')  # Log if DropBot is not connected.
    def set_voltage(self, voltage):
        """
        Set the waveform voltage.

        Parameters:
            voltage : RMS voltage
        """
        _L().info("%.1f", voltage)
        self.control_board.voltage = voltage

        # Cache measured actuation voltage. Delay before measuring the
        # actuation voltage to give it time to settle.
        gobject.timeout_add(100, lambda *args:
                            setattr(self, 'actuation_voltage',
                                    self.control_board.measure_voltage()))

    @require_connection(log_level='info')  # Log if DropBot is not connected.
    def set_frequency(self, frequency):
        """
        Set the waveform frequency.

        Parameters:
            frequency : frequency in Hz
        """
        _L().info("%.1f", frequency)
        self.control_board.frequency = frequency
        self.current_frequency = frequency

    def on_step_options_changed(self, plugin, step_number):
        app = get_app()
        if (app.protocol and not app.running and not app.realtime_mode and
            (plugin == 'microdrop.gui.dmf_device_controller' or plugin ==
             self.name) and app.protocol.current_step_number == step_number):
            _L().info('%s step #%d', plugin, step_number)
            self.on_step_run()

    def on_step_swapped(self, original_step_number, new_step_number):
        _L().info('%d -> %d', original_step_number, new_step_number)
        self.on_step_options_changed(self.name,
                                     get_app().protocol.current_step_number)

    def on_experiment_log_changed(self, log):
        '''
        Add control board metadata to the experiment log.

        .. versionchanged:: 0.16.1
            Only attempt to run diagnostic tests if DropBot hardware is
            connected.
        '''
        # Check if the experiment log already has control board meta data, and
        # if so, return.
        data = log.get("control board name")
        for val in data:
            if val:
                return

        # add the name, hardware version, id, and firmware version to the
        # experiment log metadata
        data = {}
        if self.control_board:
            data["control board name"] = \
                self.control_board.properties['display_name']
            data["control board id"] = \
                self.control_board.id
            data["control board uuid"] = \
                self.control_board.uuid
            data["control board hardware version"] = (self.control_board
                                                      .hardware_version)
            data["control board software version"] = (self.control_board
                                                      .properties
                                                      ['software_version'])
            # add info about the devices on the i2c bus
            """
            try:
                #data["i2c devices"] = (self.control_board._i2c_devices)
            except:
                pass
            """
        log.add_data(data)

        # add metadata to experiment log
        log.metadata[self.name] = data

        # run diagnostic tests
        app_values = self.get_app_values()
        if self.dropbot_connected.is_set() and app_values.get('Auto-run '
                                                              'diagnostic '
                                                              'tests'):
            _L().info('Running diagnostic tests')
            tests = ['system_info',
                     'test_i2c',
                     'test_voltage',
                     'test_shorts',
                     'test_on_board_feedback_calibration']
            results = {}

            for test in tests:
                test_func = getattr(db.hardware_test, test)
                results[test] = test_func(self.control_board)
            db.hardware_test.log_results(results, self.diagnostics_results_dir)
        else:
            _L().info('DropBot not connected - not running diagnostic tests')

        self._use_cached_capacitance_prompt()

    @gtk_threadsafe
    def _use_cached_capacitance_prompt(self):
        '''
        .. versionadded:: 0.18
        '''
        app_values = self.get_app_values()
        if (self.dropbot_connected.is_set() and (app_values['c_liquid'] > 0 or
                                                 app_values['c_filler'] > 0)):
            response = yesno('Use cached value for c<sub>liquid</sub> '
                             'and c<sub>filler</sub>?')
            # reset the cached capacitance values
            if response == gtk.RESPONSE_NO:
                self.set_app_values(dict(c_liquid=0, c_filler=0))

    def get_schedule_requests(self, function_name):
        """
        Returns a list of scheduling requests (i.e., ScheduleRequest
        instances) for the function specified by function_name.
        """
        if function_name in ['on_step_options_changed']:
            return [ScheduleRequest(self.name,
                                    'microdrop.gui.protocol_grid_controller'),
                    ScheduleRequest(self.name,
                                    'microdrop.gui.protocol_controller'),
                    ]
        elif function_name == 'on_step_run':
            return [ScheduleRequest('droplet_planning_plugin', self.name)]
        elif function_name == 'on_app_options_changed':
            return [ScheduleRequest('microdrop.app', self.name)]
        elif function_name == 'on_protocol_swapped':
            return [ScheduleRequest('microdrop.gui.protocol_grid_controller',
                                    self.name)]
        elif function_name == 'on_app_exit':
            return [ScheduleRequest('microdrop.gui.experiment_log_controller',
                                    self.name)]
        return []


PluginGlobals.pop_env()
