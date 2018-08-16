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
from concurrent.futures import ThreadPoolExecutor
from functools import wraps
import datetime as dt
import gzip
import json
import logging
import pkg_resources
import re
import threading
import time
import types
import warnings
import webbrowser

from dropbot import EVENT_ENABLE, EVENT_CHANNELS_UPDATED, EVENT_SHORTS_DETECTED
from flatland import Integer, Float, Form, Boolean
from flatland.validation import ValueAtLeast, ValueAtMost
from matplotlib.backends.backend_gtkagg import (FigureCanvasGTKAgg as
                                                FigureCanvas)
from matplotlib.figure import Figure
from logging_helpers import _L  #: .. versionadded:: 2.24
from microdrop.app_context import get_app, get_hub_uri
from microdrop.interfaces import (IElectrodeActuator, IPlugin,
                                  IWaveformGenerator)
from microdrop.plugin_helpers import (StepOptionsController, AppDataController)
from microdrop.plugin_manager import (Plugin, implements, PluginGlobals,
                                      ScheduleRequest, emit_signal,
                                      get_service_instance_by_name)
from microdrop_utility.gui import yesno
from pygtkhelpers.gthreads import gtk_threadsafe
from pygtkhelpers.ui.dialogs import animation_dialog
from pygtkhelpers.utils import gsignal
from zmq_plugin.plugin import Plugin as ZmqPlugin
import base_node_rpc as bnr
import dropbot as db
import dropbot.hardware_test
import dropbot.self_test
import dropbot.threshold
import gobject
import gtk
# XXX Use `json_tricks` rather than standard `json` to support serializing
# [Numpy arrays and scalars][1].
#
# [1]: http://json-tricks.readthedocs.io/en/latest/#numpy-arrays
import json_tricks
import numpy as np
import pandas as pd
import path_helpers as ph
import semantic_version
import si_prefix as si
import tables
import trollius as asyncio
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
    implements(IElectrodeActuator)
    implements(IWaveformGenerator)

    version = __version__
    plugin_name = str(ph.path(__file__).realpath().parent.name)

    @property
    def StepFields(self):
        """
        Expose StepFields as a property to avoid breaking code that accesses
        the StepFields member (vs through the get_step_form_class method).


        .. versionchanged:: 2.33
            Deprecate all step fields _except_ ``volume_threshold`` as part of
            refactoring to implement `IElectrodeActuator` interface.
        """
        return Form.of(#: .. versionadded:: 0.18
                       Float.named('volume_threshold')
                       .using(default=0,
                              optional=True,
                              validators=[ValueAtLeast(minimum=0),
                                          ValueAtMost(maximum=1.0)]))

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

        .. versionchanged:: 2.29
            Make `_on_dropbot_connected` function reentrant, i.e., support
            calling the function more than once.

        .. versionchanged:: 2.30
            Push changes to connection status and actuation area to statusbar.

        .. versionchanged:: 2.31
            Display an error message when the DropBot reports that shorts have
            been detected on one or more channels.

        .. versionchanged:: 2.32
            Display an error message when a "halted" event is received from the
            DropBot.
        '''
        # Explicitly initialize GObject base class since it is not the first
        # base class listed.
        gobject.GObject.__init__(self)

        #: ..versionadded:: 2.33
        self.executor = ThreadPoolExecutor()
        #: ..versionadded:: 2.33
        self._capacitance_log_lock = threading.Lock()

        self.control_board = None
        self.name = self.plugin_name
        self.connection_status = "Not connected"
        self.current_frequency = None
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
        self.capacitance_watch_thread = None
        #: .. versionadded:: 2.24
        self.capacitance_exceeded = threading.Event()
        #: .. versionadded:: 2.33
        self._actuation_completed = threading.Event()

        self.chip_watch_thread = None
        self._chip_inserted = threading.Event()
        self._dropbot_connected = threading.Event()
        self.dropbot_connected.count = 0

        self.connect('chip-inserted', lambda *args:
                     self.chip_inserted.set())
        self.connect('chip-inserted', lambda *args:
                     self.update_connection_status())
        self.connect('chip-removed', lambda *args:
                     self.chip_inserted.clear())
        self.connect('chip-removed', lambda *args:
                     self.update_connection_status())
        self.connect('chip-removed', lambda *args: self.clear_status())

        def _connect_dropbot_signals(*args):
            '''
            .. versionadded:: 2.29

            .. versionchanged:: 2.29
                Tie connection status to serial connection signals.

            .. versionchanged:: 2.31
                Display an error message when the DropBot reports that shorts
                have been detected on one or more channels.

            .. versionchanged:: 2.32
                Display an error message when "halted" event is received from
                the DropBot.
            '''
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
            _L().info('connected capacitance updated signal callback')

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
                # m^2 area
                area = self.actuated_area * (1e-3 ** 2)
                # Approximate area in SI units.
                value, pow10 = si.split(np.sqrt(area))
                si_unit = si.SI_PREFIX_UNITS[len(si.SI_PREFIX_UNITS) // 2 + pow10 / 3]
                status = ('actuated electrodes: %s (%.1f %sm^2)' %
                          (self.actuated_channels, value ** 2, si_unit))
                self.push_status(status, None, True)
                _L().debug(status)
                self._state_applied.set()

            (self.control_board.signals.signal('channels-updated')
             .connect(_on_channels_updated, weak=False))
            _L().info('connected channels updated signal callback')

            @gtk_threadsafe
            def refresh_channels():
                # XXX Reassign channel states to trigger a `channels-updated`
                # message since actuated channel states may have changed based
                # on the channels that were disabled.
                self.control_board.turn_off_all_channels()
                self.control_board.state_of_channels = self.channel_states

            @gtk_threadsafe
            def _on_shorts_detected(message):
                '''
                Example message:

                ```python
                OrderedDict([(u'event', u'shorts-detected'), (u'values', [])])
                ```
                '''
                if message.get('values'):
                    status = ('Shorts detected.  Disabled the following '
                              'channels: %s' % message['values'])
                    _L().error('Shorts were detected on the following '
                               'channels:\n\n    %s\n\n'
                               'You may continue using the DropBot, but the '
                               'affected channels have been disabled until the'
                               ' DropBot is restarted (e.g., unplug all cables'
                               ' and plug back in).', message['values'])
                else:
                    status = 'No shorts detected.'
                # XXX Refresh channels since some channels may have been
                # disabled.
                refresh_channels()
                self.push_status(status)

            (self.control_board.signals.signal('shorts-detected')
             .connect(_on_shorts_detected, weak=False))

            @gtk_threadsafe
            def on_serial_connected(message):
                self.emit('dropbot-connected', self.control_board)

            @gtk_threadsafe
            def on_serial_disconnected(message):
                self.emit('dropbot-disconnected')

            (self.control_board.serial_signals.signal('connected')
             .connect(on_serial_connected, weak=False))
            (self.control_board.serial_signals.signal('disconnected')
             .connect(on_serial_disconnected, weak=False))

            @gtk_threadsafe
            def _on_halted(message):
                # DropBot has halted.  All channels have been disabled and high
                # voltage has been turned off.

                reason =  ''

                if 'error' in message:
                    error = message['error']
                    if error.get('name') == 'output-current-exceeded':
                        reason = ' because output current was exceeded'
                    elif error.get('name') == 'chip-load-saturated':
                        reason = ' because chip load feedback exceeded allowable range'

                status = 'DropBot has halted%s.' % reason
                message = '''
                    All channels have been disabled and high voltage has been
                    turned off until the DropBot is restarted (e.g., unplug all
                    cables and plug back in).'''.strip()
                # XXX Refresh channels since channels were disabled.
                refresh_channels()
                self.push_status(status)
                _L().error('\n'.join([status, map(str.strip,
                                                  message.splitlines())]))

            self.control_board.signals.signal('halted').connect(_on_halted,
                                                                weak=False)

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

            .. versionchanged:: 2.29
                Make function reentrant, i.e., support calling this function
                more than once.  This may be useful, e.g., for supporting
                DropBot reconnects.

            .. versionchanged:: 2.32.1
                Enable DropBot ``shorts-detected`` events by setting the
                respective bit in the event mask.  Fixes bug introduced in
                2.31.
            '''
            if self.dropbot_connected.count < 1:
                # This is the initial connection.  Connect signal callbacks.
                _connect_dropbot_signals()
                message = ('Initial connection to DropBot established. '
                           'Connected signal callbacks.')
                _L().debug(message)
                self.push_status(message)
            else:
                # DropBot signal callbacks have already been connected.
                message = ('DropBot connection re-established.')
                _L().debug(message)
                self.push_status(message)
            self.dropbot_connected.count += 1

            # Set event indicating DropBot has been connected.
            self.dropbot_connected.set()

            # Request for the DropBot to measure the device load capacitance
            # every 100 ms.
            app_values = self.get_app_values()
            self.control_board.update_state(capacitance_update_interval_ms=
                                            app_values['c_update_ms'],
                                            event_mask=EVENT_CHANNELS_UPDATED |
                                            EVENT_SHORTS_DETECTED |
                                            EVENT_ENABLE)

            OUTPUT_ENABLE_PIN = 22
            # Chip may have been inserted before connecting, so `chip-inserted`
            # event may have been missed.
            # Explicitly check if chip is inserted by reading **active low**
            # `OUTPUT_ENABLE_PIN`.
            if self.control_board.digital_read(OUTPUT_ENABLE_PIN):
                self.emit('chip-removed')
            else:
                self.emit('chip-inserted')
                gtk_threadsafe(lambda: self.control_board.detect_shorts(5) and
                               False)()

            self.device_time_sync = {'host': dt.datetime.utcnow(),
                                     'device_us':
                                     self.control_board.microseconds()}

        self.connect('dropbot-connected', _on_dropbot_connected)

        def _on_dropbot_disconnected(*args):
            self.push_status('DropBot connection lost.')
            # Clear capacitance exceeded event since DropBot is not connected.
            self.capacitance_exceeded.clear()
            # Clear event indicating DropBot has been disconnected.
            self.dropbot_connected.clear()
            self.emit('chip-removed')

        self.connect('dropbot-disconnected', _on_dropbot_disconnected)

    @gtk_threadsafe
    def clear_status(self):
        '''
        Clear statusbar context for this plugin.


        .. versionadded:: 2.30
        '''
        app = get_app()
        statusbar = app.builder.get_object('statusbar')
        context_id = statusbar.get_context_id(self.name)

        statusbar.remove_all(context_id)

    @gtk_threadsafe
    def push_status(self, status, hide_timeout_s=3, clear=True):
        '''
        Push status message to statusbar context for this plugin.

        Parameters
        ----------
        status : str
            Status message.
        hide_timeout_s : float, optional
            Number of seconds to display message before hiding.  If `None`, do
            not hide.
        clear : bool, optional
            Clear existing statusbar stack before pushing new status.


        .. versionadded:: 2.30
        '''
        app = get_app()
        statusbar = app.builder.get_object('statusbar')
        context_id = statusbar.get_context_id(self.name)

        if clear:
            statusbar.remove_all(context_id)

        message_id = statusbar.push(context_id, '[%s] %s' % (self.name, status))

        if hide_timeout_s is not None:
            # Hide status message after specified timeout.
            gobject.timeout_add(int(hide_timeout_s * 1e3),
                                statusbar.remove_message, context_id,
                                message_id)

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
                             'may take up to a minute to complete.  Please '
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

    def cleanup_plugin(self):
        '''
        .. versionchanged:: 2.25
            Kill any currently running step.
        '''
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
            gtk_threadsafe(self.create_ui)()

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

    def on_plugin_disable(self):
        self.cleanup_plugin()

    def on_app_exit(self):
        """
        Handler called just before the Microdrop application exits.

        .. versionchanged:: 0.19
            Emit ``dropbot-disconnected`` ``gsignal`` after closing DropBot
            connection.

        .. versionchanged:: 2.33
            Delegate all clean-up to :meth:`cleanup_plugin()`.
        """
        self.cleanup_plugin()

    def on_app_options_changed(self, plugin_name):
        '''
        .. versionchanged:: 0.22.2
            Remove check for serial port, which is no longer used as of version
            0.22.

        .. versionchanged:: 2.26
            Apply specified capacitance update interval to DropBot (if
            connected).

        .. versionchanged:: 2.30
            Clear statusbar context when real-time mode is disabled.
        '''
        # XXX TODO implement `IApplicationMode` interface (see https://trello.com/c/zxwRlytP)
        app = get_app()
        if plugin_name == app.name:
            # Turn off all electrodes if we're not in realtime mode and not
            # running a protocol.
            if self.dropbot_connected.is_set():
                app_values = self.get_app_values()
                self.control_board.update_state(capacitance_update_interval_ms=
                                                app_values['c_update_ms'])
                if not app.realtime_mode and not app.running:
                    _L().info('Turning off all electrodes.')
                    self.control_board.hv_output_enabled = False
                    self.update_connection_status()
                    self.clear_status()

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

            .. versionchanged:: 2.33
                Fix connection of DropBot signals when plugin is disabled and
                re-enabled.
            '''
            try:
                self.dropbot_connected.count = 0
                self.dropbot_connected.clear()
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

    @gtk_threadsafe
    def _calibrate_device_capacitance(self, name):
        '''
        .. versionadded:: 0.18

        .. versionchanged:: 2.33
            Refactor to use ``microdrop.electrode_controller_plugin`` step
            options for frequency, voltage, and channels.
        '''
        plugin = get_service_instance_by_name('microdrop'
                                              '.electrode_controller_plugin',
                                              env='microdrop')
        if not self.dropbot_connected.is_set():
            _L().error('DropBot is not connected.')
        else:
            with self.control_board.transaction_lock:
                # Save original state to restore later.
                original_state = self.control_board.state
                channel_states = self.control_board.state_of_channels

                options = plugin.get_step_options()
                try:
                    states = options['electrode_states'].copy()
                    # Index requested actuation states by channel rather than
                    # electrode.
                    app = get_app()
                    states.index = (app.dmf_device.channels_by_electrode
                                    .loc[states.index])

                    actuated_electrodes = \
                        db.threshold.actuate_channels(self.control_board,
                                                      states[states > 0].index,
                                                      timeout=5)

                    if not actuated_electrodes:
                        _L().error('At least one electrode must be actuated to'
                                   ' perform calibration.')
                        return

                    # Set output voltage and frequency.
                    emit_signal("set_frequency",
                                options['Frequency (Hz)'],
                                interface=IWaveformGenerator)
                    emit_signal("set_voltage", options['Voltage (V)'],
                                interface=IWaveformGenerator)

                    # Measure absolute capacitance and compute _specific_
                    # capacitance (i.e., capacitance per mm^2).
                    c = self.control_board.measure_capacitance()
                    app_values = {}
                    app_values['c_%s' % name] = c / self.actuated_area
                    self.set_app_values(app_values)

                    message = ('Measured %s capacitance: %sF/%.1f mm^2 = %sF/mm^2'
                            % (name, si.si_format(c), self.actuated_area,
                                si.si_format(c / self.actuated_area)))
                    _L().info(message)
                    gtk_threadsafe(self.push_status)(message, 10, False)

                    # send a signal to update the gui
                    emit_signal('on_device_capacitance_update', c)
                finally:
                    # Restore original control board state.
                    state = self.control_board.state
                    if not (state == original_state).all():
                        self.control_board.state = \
                            original_state[state != original_state]
                    self.control_board.state_of_channels = channel_states

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
        logger = _L()  # use logger with method context
        logger.debug('logging %s capacitance updates',
                     len(capacitance_updates))
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
                  ((df['time_us'] - self.device_time_sync['device_us']) *
                   1e-6).map(lambda x: dt.timedelta(seconds=x)))
        df.insert(2, 'step', app.protocol.current_step_number + 1)
        # Drop `start` and `end` columns since relevant time information is
        # stored in `timestamp_utc`.
        df.drop(['time_us'], axis=1, inplace=True)

        with self._capacitance_log_lock:
            # Use `compresslevel=1` to prioritize compression speed while still
            # significantly reducing the output file size compared to no
            # compression.
            #
            # See [here][1] for some supporting motivation.
            #
            # [1]: https://github.com/gruntjs/grunt-contrib-compress/issues/116#issuecomment-70883022
            with gzip.open(csv_output_path, 'a', compresslevel=1) as output:
                df.to_csv(output, index=False, header=include_header)
        logger.info('logged %s capacitance updates to `%s`', df.shape[0],
                    csv_output_path)

    def on_protocol_run(self):
        """
        Handler called when a protocol starts running.
        """
        # XXX TODO 2.33 refactor to implement `IApplicationMode` interface
        # XXX TODO implement `IApplicationMode` interface (see https://trello.com/c/zxwRlytP)
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
        # XXX TODO 2.33 refactor to implement `IApplicationMode` interface
        # XXX TODO implement `IApplicationMode` interface (see https://trello.com/c/zxwRlytP)
        app = get_app()
        if self.dropbot_connected.is_set() and not app.realtime_mode:
            # Turn off all electrodes
            _L().debug('Turning off all electrodes.')
            self.control_board.hv_output_enabled = False

    @require_connection(log_level='info')  # Log if DropBot is not connected.
    def set_voltage(self, voltage):
        """
        Set the waveform voltage.

        Parameters:
            voltage : RMS voltage


        .. versionchanged:: 2.33
            Ensure high-voltage output is turned on and enabled.
        """
        _L().debug("%.1f", voltage)

        with self.control_board.transaction_lock:
            original_state = self.control_board.state

            # Construct required state
            state = original_state.copy()
            state.hv_output_enabled = True
            state.hv_output_selected = True

            if not (state == original_state).all():
                # Update modified state properties.
                self.control_board.state = state[state != original_state]

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
        _L().debug("%.1f", frequency)
        self.control_board.frequency = frequency
        self.current_frequency = frequency

    @asyncio.coroutine
    def on_actuation_request(self, electrode_states, duration_s=0):
        '''
        XXX Coroutine XXX

        Actuate electrodes according to specified states.

        Parameters
        ----------
        electrode_states : pandas.Series
        duration_s : float, optional
            If ``volume_threshold`` step option is set, maximum duration before
            timing out.  Otherwise, time to actuate before actuation is
            considered completed.

        Returns
        -------
        actuated_electrodes : list
            List of actuated electrode IDs.


        .. versionadded:: 2.33
        '''
        if not self.dropbot_connected.is_set():
            raise RuntimeError('DropBot not connected.')

        app = get_app()
        options = self.get_step_options()
        app_values = self.get_app_values()
        requested_electrodes = electrode_states[electrode_states > 0].index
        requested_channels = (app.dmf_device.channels_by_electrode
                              .loc[requested_electrodes])

        # Criteria that must be met to set target capacitance.
        threshold_criteria = [app.running, duration_s > 0,
                              options['volume_threshold'] > 0,
                              len(requested_electrodes) > 0,
                              app_values['c_liquid'] > 0]

        if not all(threshold_criteria):
            # ## Case 1: no volume threshold specified.
            #  1. Set control board state of channels according to requested
            #     actuation states.
            #  2. Wait for channels to be actuated.
            actuated_channels = \
                db.threshold.actuate_channels(self.control_board,
                                              requested_channels, timeout=5)

            #  3. Connect to `capacitance-updated` signal to record capacitance
            #     values measured during the step.
            capacitance_messages = []

            def _on_capacitance_updated(message):
                message['actuated_channels'] = self.actuated_channels
                message['actuated_area'] = self.actuated_area
                capacitance_messages.append(message)

            (self.control_board.signals.signal('capacitance-updated')
             .connect(_on_capacitance_updated))
            #  4. Delay for specified duration.
            try:
                yield asyncio.From(asyncio.sleep(duration_s))
            finally:
                (self.control_board.signals.signal('capacitance-updated')
                 .disconnect(_on_capacitance_updated))
        else:
            # ## Case 2: volume threshold specified.
            #
            # A volume threshold has been set for this step.

            # Calculate target capacitance based on actuated area.
            #
            # Note: `app_values['c_liquid']` represents a *specific
            # capacitance*, i.e., has units of $F/mm^2$.
            actuated_areas = (app.dmf_device.electrode_areas
                              .ix[requested_electrodes.values])
            actuated_area = actuated_areas.sum()

            meters_squared_area = actuated_area * (1e-3 ** 2)  # m^2 area
            # Approximate length of unit side in SI units.
            si_length, pow10 = si.split(np.sqrt(meters_squared_area))
            si_unit = si.SI_PREFIX_UNITS[len(si.SI_PREFIX_UNITS) // 2 + pow10 /
                                         3]

            target_capacitance = (options['volume_threshold'] * actuated_area *
                                  app_values['c_liquid'])

            logger = _L()  # use logger with function context
            if logger.getEffectiveLevel() <= logging.DEBUG:
                message = ('target capacitance: %sF (actuated area: (%.1f '
                           '%sm^2) actuated channels: %s)' %
                           (si.si_format(target_capacitance), si_length ** 2,
                            si_unit, requested_channels))
                map(logger.debug, message.splitlines())
            # Wait for target capacitance to be reached in background thread,
            # timing out if the specified duration is exceeded.
            co_future = \
                db.threshold.co_target_capacitance(self.control_board,
                                                   requested_channels,
                                                   target_capacitance,
                                                   allow_disabled=False,
                                                   timeout=duration_s)
            try:
                dropbot_event = yield asyncio.From(asyncio
                                                   .wait_for(co_future,
                                                             duration_s))
                _L().debug('target capacitance reached: `%s`', dropbot_event)
                actuated_channels = dropbot_event['actuated_channels']

                capacitance_messages = dropbot_event['capacitance_updates']
                # Add actuated area to capacitance update messages.
                for capacitance_i in capacitance_messages:
                    capacitance_i['acuated_area'] = actuated_area

                # Show notification in main window status bar.
                status = ('reached %sF (> %sF) over electrodes: %s (%.1f '
                          '%sm^2) after %ss' %
                          (si.si_format(dropbot_event['new_value']),
                           si.si_format(dropbot_event['target']),
                           actuated_channels, si_length ** 2, si_unit,
                           (dropbot_event['end'] -
                            dropbot_event['start']).total_seconds()))
                gtk_threadsafe(self.push_status)(status, 5, False)
            except asyncio.TimeoutError:
                raise RuntimeError('Timed out waiting for target capacitance.')

        actuated_electrodes = (app.dmf_device.electrodes_by_channel
                               .loc[actuated_channels])

        # Write capacitance updates to log in background thread.
        self.executor.submit(self.log_capacitance_updates,
                             capacitance_messages)

        # Return list of actuated channels (which _may_ be fewer than the
        # number of requested actuated channels if one or more channels is
        # _disabled_).
        raise asyncio.Return(actuated_electrodes)

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
        # XXX TODO add event to indicate if `c_liquid` has been confirmed; either by prompting to use cached value or by measuring new value.
        # XXX TODO add event to indicate if `c_filler` has been confirmed; either by prompting to use cached value or by measuring new value.
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
        if function_name == 'on_app_options_changed':
            return [ScheduleRequest('microdrop.app', self.name)]
        elif function_name == 'on_protocol_swapped':
            return [ScheduleRequest('microdrop.gui.protocol_grid_controller',
                                    self.name)]
        elif function_name == 'on_app_exit':
            return [ScheduleRequest('microdrop.gui.experiment_log_controller',
                                    self.name)]
        return []


PluginGlobals.pop_env()
