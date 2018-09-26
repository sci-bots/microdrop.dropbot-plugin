from __future__ import division
from concurrent.futures import ThreadPoolExecutor
from functools import wraps
import datetime as dt
import gzip
import re
import threading
import time
import types
import warnings
import webbrowser

from asyncio_helpers import cancellable, sync
from debounce.async import Debounce
from dropbot import EVENT_ENABLE, EVENT_CHANNELS_UPDATED, EVENT_SHORTS_DETECTED
from flatland import Integer, Float, Form, Boolean
from flatland.validation import ValueAtLeast, ValueAtMost
from matplotlib.backends.backend_gtkagg import (FigureCanvasGTKAgg as
                                                FigureCanvas)
from matplotlib.figure import Figure
from logging_helpers import _L  #: .. versionadded:: 2.24
from microdrop.app_context import (get_app, get_hub_uri, MODE_RUNNING_MASK,
                                   MODE_REAL_TIME_MASK)
from microdrop.interfaces import (IApplicationMode, IElectrodeActuator,
                                  IPlugin, IWaveformGenerator)
from microdrop.plugin_helpers import (StepOptionsController, AppDataController,
                                      hub_execute)
from microdrop.plugin_manager import (Plugin, implements, PluginGlobals,
                                      ScheduleRequest, emit_signal,
                                      get_service_instance_by_name)
from microdrop_utility.gui import yesno
from pygtkhelpers.gthreads import gtk_threadsafe
from pygtkhelpers.ui.dialogs import animation_dialog
from zmq_plugin.plugin import Plugin as ZmqPlugin
from zmq_plugin.schema import decode_content_data
import blinker
import dropbot as db
import dropbot.hardware_test
import dropbot.monitor
import dropbot.self_test
import dropbot.threshold
import gobject
import gtk
# XXX Use `json_tricks` rather than standard `json` to support serializing
# [Numpy arrays and scalars][1].
#
# [1]: http://json-tricks.readthedocs.io/en/latest/#numpy-arrays
import json_tricks
import markdown2pango
import numpy as np
import pandas as pd
import path_helpers as ph
import si_prefix as si
import tables
import trollius as asyncio
import zmq

from ._version import get_versions
from .noconflict import classmaker
from .execute import execute
__version__ = get_versions()['version']
del get_versions


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
        return True

    def on_execute__measure_liquid_capacitance(self, request):
        self.parent.on_measure_liquid_capacitance()

    def on_execute__measure_filler_capacitance(self, request):
        self.parent.on_measure_filler_capacitance()

    def on_execute__find_liquid(self, request):
        return self.parent.find_liquid()

    def on_execute__identify_electrode(self, request):
        data = decode_content_data(request)
        self.parent.identify_electrode(data['electrode_id'])


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

    .. versionchanged:: 2.35
        Set default focus to OK button.
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

        # Set default focus to OK button.
        buttons = {b.props.label: b
                   for b in dialog.get_action_area().get_children()}
        ok_button = buttons['gtk-ok']
        ok_button.props.has_focus = True
        ok_button.props.has_default = True

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
    implements(IPlugin)
    implements(IApplicationMode)
    implements(IElectrodeActuator)
    implements(IWaveformGenerator)

    version = __version__
    plugin_name = 'dropbot_plugin'

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
        self.channel_states = pd.Series()
        self.plugin = None
        self.plugin_timeout_id = None
        self.menu_items = []
        self.menu = None
        self.menu_item_root = None
        self.diagnostics_results_dir = ph.path('.dropbot-diagnostics')
        self.actuated_area = 0
        self.monitor_task = None

        #: .. versionadded:: 2.24
        self.device_time_sync = {}

        self._chip_inserted = threading.Event()
        self._dropbot_connected = threading.Event()
        self.dropbot_connected.count = 0

        self.dropbot_signals = blinker.Namespace()

        @asyncio.coroutine
        def on_inserted(sender, **message):
            self.chip_inserted.set()
            self.update_connection_status()

        self.dropbot_signals.signal('chip-inserted').connect(on_inserted,
                                                             weak=False)

        @asyncio.coroutine
        def on_removed(sender, **message):
            self.chip_inserted.clear()
            self.update_connection_status()
            self.clear_status()

        self.dropbot_signals.signal('chip-removed').connect(on_removed,
                                                            weak=False)

        # Update cached device load capacitance each time the
        # `'capacitance-updated'` signal is emitted from the DropBot.
        def _on_capacitance_updated(sender, **message):
            self.on_device_capacitance_update(message['new_value'],
                                              message['V_a'])

        # Call capacitance update callback _at most_ every 200 ms.
        self.dropbot_signals.signal('capacitance-updated')\
            .connect(asyncio.coroutine(Debounce(_on_capacitance_updated, 100,
                                                max_wait=200, leading=True)),
                     weak=False)

        @asyncio.coroutine
        def _on_channels_updated(sender, **message):
            '''
            Message keys:
             - ``"n"``: number of actuated channel
             - ``"actuated"``: list of actuated channel identifiers.
             - ``"start"``: ms counter before setting shift registers
             - ``"end"``: ms counter after setting shift registers
            '''
            actuated_channels = message['actuated']
            if actuated_channels:
                app = get_app()
                actuated_electrodes = \
                    (app.dmf_device.actuated_electrodes(actuated_channels)
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
            si_unit = si.SI_PREFIX_UNITS[len(si.SI_PREFIX_UNITS) // 2 +
                                         pow10 // 3]
            status = ('actuated electrodes: %s (%.1f %sm^2)' %
                      (actuated_channels, value ** 2, si_unit))
            self.push_status(status, None, True)
            _L().debug(status)

        self.dropbot_signals.signal('channels-updated')\
            .connect(_on_channels_updated, weak=False)

        @gtk_threadsafe
        def refresh_channels():
            # XXX Reassign channel states to trigger a `channels-updated`
            # message since actuated channel states may have changed based
            # on the channels that were disabled.
            self.control_board.turn_off_all_channels()
            self.control_board.state_of_channels = self.channel_states

        @asyncio.coroutine
        def _on_shorts_detected(sender, **message):
            '''
            Example message:

            ```python
            OrderedDict([(u'event', u'shorts-detected'), (u'values', [])])
            ```
            '''
            if message.get('values'):
                status = ('Shorts detected.  Disabled the following '
                          'channels: %s' % message['values'])
                gtk_threadsafe(_L().error)\
                ('Shorts were detected on the following '
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

        self.dropbot_signals.signal('shorts-detected')\
            .connect(_on_shorts_detected, weak=False)

        @asyncio.coroutine
        def _on_halted(sender, **message):
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
            gtk_threadsafe(_L().error)\
                ('\n'.join([status, map(str.strip, message.splitlines())]))

        self.dropbot_signals.signal('halted').connect(_on_halted, weak=False)

        @asyncio.coroutine
        def _on_dropbot_connected(sender, **message):
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
            dropbot_ = message['dropbot']
            map(_L().info, str(dropbot_.properties).splitlines())
            self.control_board = dropbot_
            if self.dropbot_connected.count < 1:
                status = 'Initial connection to DropBot established.'
                _L().debug(status)
                self.push_status(status)
            else:
                # DropBot signal callbacks have already been connected.
                status = ('DropBot connection re-established.')
                _L().debug(status)
                self.push_status(status)
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
            self.device_time_sync = {'host': dt.datetime.utcnow(),
                                     'device_us':
                                     self.control_board.microseconds()}
            self.update_connection_status()

        self.dropbot_signals.signal('connected').connect(_on_dropbot_connected,
                                                         weak=False)

        @asyncio.coroutine
        def _on_dropbot_disconnected(sender, **message):
            self.push_status('DropBot connection lost.')
            # Clear event indicating DropBot has been disconnected.
            self.dropbot_connected.clear()
            self.control_board = None
            self.update_connection_status()

        self.dropbot_signals.signal('disconnected')\
            .connect(_on_dropbot_disconnected, weak=False)

        @asyncio.coroutine
        def on_version_mismatch(*args, **kwargs):
            message = ('**DropBot driver** version `%(driver_version)s` does '
                       'not match **firmware** version `%(firmware_version)s`.'
                       % kwargs)

            @sync(gtk_threadsafe)
            def version_mismatch_dialog():
                parent = get_app().main_window_controller.view
                dialog = gtk.Dialog('DropBot driver version mismatch',
                                    buttons=('_Update', gtk.RESPONSE_ACCEPT,
                                             '_Ignore', gtk.RESPONSE_OK,
                                             '_Skip', gtk.RESPONSE_NO),
                                    flags=gtk.DIALOG_MODAL |
                                    gtk.DIALOG_DESTROY_WITH_PARENT,
                                    parent=parent)
                # Disable dialog window close "X" button.
                dialog.props.deletable = False

                # Do not close window when <Escape> key is pressed.
                #
                # See: http://www.async.com.br/faq/pygtk/index.py?req=show&file=faq10.013.htp
                def on_response(dialog, response):
                    if response in (gtk.RESPONSE_DELETE_EVENT, gtk.RESPONSE_CLOSE):
                        dialog.emit_stop_by_name('response')

                dialog.connect('delete_event', lambda *args: True)
                dialog.connect('response', on_response)
                dialog.connect('close', lambda *args: True)

                buttons = {'ignore':
                           dialog.get_widget_for_response(gtk.RESPONSE_OK),
                           'update':
                           dialog.get_widget_for_response(gtk.RESPONSE_ACCEPT),
                           'skip':
                           dialog.get_widget_for_response(gtk.RESPONSE_NO)}
                buttons['ignore']\
                    .set_tooltip_text('Ignore driver version mismatch and '
                                      'connect anyway.')
                buttons['update']\
                    .set_tooltip_text('Upload DropBot firmware to match driver'
                                      ' version.')
                buttons['skip'].set_tooltip_text('Do not connect to DropBot.  '
                                                 'Unplug DropBot to avoid this'
                                                 ' dialog.')

                content_area = dialog.get_content_area()
                label = gtk.Label(markdown2pango.markdown2pango(message))
                label.props.use_markup = True
                label.props.wrap = True
                label.props.xpad = 20
                label.props.ypad = 20
                label.props.height_request = 200
                label.props.height_request = 100
                # Align text to top left of dialog.
                label.set_alignment(0, 0)
                content_area.pack_start(label, expand=True, fill=True)
                content_area.show_all()
                try:
                    response = dialog.run()
                    response_button = dialog.get_widget_for_response(response)
                    response_str = [b[0] for b in buttons.items()
                                    if b[1] == response_button][0]
                    return response_str
                finally:
                    dialog.destroy()

            response = yield asyncio.From(version_mismatch_dialog())

            if response == 'skip':
                raise IOError(message)
            raise asyncio.Return(response)

        self.dropbot_signals.signal('version-mismatch')\
            .connect(on_version_mismatch, weak=False)

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

        .. versionchanged:: 2.35
            Use :meth:`run_tests()` to execute tests while displaying a
            progress dialog indicating which test is currently running.
        '''
        # XXX Wait for test results in background thread to allow UI to display
        # and update a progress dialog.
        future = self.executor.submit(self.run_tests().result)

        def _on_tests_completed(future):
            results = future.result()
            # Tests have completed, now:
            #
            #  1. Write HTML report to `.dropbot-diagnostics` directory in current
            #     working directory (with raw JSON results embedded in a
            #     `<script id="results" .../> tag).
            #  2. Launch HTML report in web browser.
            results_dir = ph.path(self.diagnostics_results_dir)
            results_dir.makedirs_p()

            # Create unique output filenames based on current timestamp.
            timestamp = dt.datetime.utcnow().isoformat().replace(':', '_')
            report_path = results_dir.joinpath('results-%s.html' % timestamp)

            # Generate test result summary report as HTML document.
            db.self_test.generate_report(results, output_path=report_path,
                                         force=True)
            # Launch HTML report.
            report_path.launch()

        future.add_done_callback(_on_tests_completed)

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

        .. versionchanged:: 2.34.1
            Add ``_DropBot help...`` entry to main window ``Help`` menu.

        .. versionchanged:: 2.37
            Replace original MicroDrop help menu item.
        '''
        # Add DropBot help entry to main window `Help` menu.
        menu_item = gtk.ImageMenuItem(stock_id=gtk.STOCK_HELP)
        menu_item.set_label('_DropBot help...')
        help_url = 'https://sci-bots.com/dropbot'
        menu_item.connect('activate', lambda menu_item:
                          webbrowser.open_new_tab(help_url))
        app = get_app()
        main_help_menu = app.builder.get_object('menu_help')
        main_help_menu.insert(menu_item, len(main_help_menu.get_children()) -
                              1)
        menu_item.show()

        # Remove original MicroDrop help menu item (if it exists).
        for c in main_help_menu.get_children()[:]:
            if c.props.label == 'Online _help...':
                main_help_menu.remove(c)

        # Create head for DropBot on-board tests sub-menu.
        tests_menu_head = gtk.MenuItem('On-board self-_tests')

        # Create DropBot tools menu.
        self.menu_items = [gtk.MenuItem('Run _all on-board self-tests...'),
                           tests_menu_head]
        self.menu_items[0].connect('activate', lambda menu_item:
                                   self.run_all_tests())

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

        .. versionchanged:: 2.34.1
            Do not enable ``"Auto-run diagnostic tests"`` by default.

        .. versionchanged:: 2.36
            Deprecate actuation default settings since the respective step
            options were deprecated as part of refactoring to implement
            `IElectrodeActuator` interface.
        '''
        return Form.of(
            Boolean.named('Auto-run diagnostic tests').using(default=False,
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

        .. versionchanged:: X.X.X
            Stop background DropBot connection monitor task.
        '''
        if self.plugin_timeout_id is not None:
            gobject.source_remove(self.plugin_timeout_id)
        if self.plugin is not None:
            self.plugin = None
        self.stop_monitor()

    def on_plugin_enable(self):
        '''
        .. versionchanged:: 0.19
            Launch background thread to monitor for DMF chip status events from
            DropBot serial stream.

        .. versionchanged:: 2.22.4
            Initialize connection status before attempting to connect to
            DropBot.  This allows, for example, menu items requiring a DropBot
            to default to non-sensitive.

        .. versionchanged:: 2.36
            Register ``identify_electrode()`` electrode command with command
            plugin.
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
        self.plugin = DmfZmqPlugin(self, self.name, get_hub_uri())
        # Initialize sockets.
        self.plugin.reset()

        # Periodically process outstanding message received on plugin sockets.
        self.plugin_timeout_id = gtk.timeout_add(10, self.plugin.check_sockets)

        # Register electrode commands.
        for medium in ('liquid', 'filler'):
            hub_execute('microdrop.command_plugin', 'register_command',
                        command_name='measure_%s_capacitance' % medium,
                        namespace='global', plugin_name=self.name,
                        title='Measure _%s capacitance' % medium)
        hub_execute('microdrop.command_plugin', 'register_command',
                    command_name='find_liquid', namespace='global',
                    plugin_name=self.name, title='Fin_d liquid')
        hub_execute('microdrop.command_plugin', 'register_command',
                    command_name='identify_electrode', namespace='electrode',
                    plugin_name=self.name, title='_Visually identify '
                    'electrode')

        self.start_monitor()

    def start_monitor(self):
        '''
        .. versionadded:: X.X.X

        Start DropBot connection monitor task.
        '''
        if self.monitor_task is not None:
            self.monitor_task.cancel()
            self.control_board = None
            self.dropbot_connected.clear()

        @asyncio.coroutine
        def dropbot_monitor(*args):
            try:
                yield asyncio.From(db.monitor.monitor(*args))
            except asyncio.CancelledError:
                _L().info('Stopped DropBot monitor.')

        self.monitor_task = cancellable(dropbot_monitor)
        thread = threading.Thread(target=self.monitor_task,
                                  args=(self.dropbot_signals, ))
        thread.daemon = True
        thread.start()

    def stop_monitor(self):
        '''
        .. versionadded:: X.X.X

        Stop DropBot connection monitor task.
        '''
        if self.dropbot_connected.is_set():
            self.dropbot_connected.clear()
            if self.control_board is not None:
                self.control_board.hv_output_enabled = False
            self.control_board = None
            self.monitor_task.cancel()
            self.monitor_task = None
            gtk_threadsafe(self.update_connection_status)()

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
                    self.turn_off()

    @require_connection(log_level='info')  # Log if DropBot is not connected.
    def turn_off(self):
        '''
        .. versionadded:: 2.37

        Turn off high voltage output and clear status label and status bar.
        '''
        _L().info('Turning off all electrodes.')
        self.control_board.turn_off_all_channels()
        self.control_board.hv_output_enabled = False
        self.update_connection_status()
        self.push_status('Turned off all electrodes.')

    def data_dir(self):
        '''
        .. versionadded:: 0.18
        '''
        app = get_app()
        data_dir = app.experiment_log.get_log_path().joinpath(self.name)
        if not data_dir.isdir():
            data_dir.makedirs_p()
        return data_dir

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
        emit_signal('on_device_capacitance_update', [c, v])
        return dict(capacitance=c, voltage=v)

    def on_device_capacitance_update(self, capacitance, actuation_voltage):
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
        voltage = actuation_voltage

        app = get_app()
        app_values = self.get_app_values()
        c_liquid = app_values['c_liquid']
        if c_liquid == np.inf:
            c_liquid = 0

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
                    v = self.control_board.measure_voltage()
                    emit_signal('on_device_capacitance_update', [c, v])
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

    @asyncio.coroutine
    def on_step_run(self, plugin_kwargs, signals):
        '''
        .. versionadded:: 2.37

        Handler called whenever a step is executed.

        Parameters
        ----------
        plugin_kwargs : dict
            Plugin settings as JSON serializable dictionary.
        signals : blinker.Namespace
            Signals namespace.


        .. versionchanged:: 2.37.1
            Restore logging of capacitance update messages collected during
            actuation and notification of volume threshold reached through
            statusbar.
        '''
        app = get_app()
        dmf_device = app.dmf_device
        proxy = self.control_board

        if proxy is None and plugin_kwargs[self.name]['volume_threshold'] > 0:
            # Volume threshold is specified, but no DropBot is connected.
            # The expected behaviour _with_ DropBot connected is that specified
            # duration is _maximum_ time to wait for volume threshold to be
            # reached.
            # Rather than wait the full specified duration for each actuation,
            # set the duration to 0.2 seconds during this step to mimic typical
            # maximum actuation speed, e.g., when volume threshold is set with
            # the test board inserted.
            key = 'Duration (s)'
            plugin_kwargs['microdrop.electrode_controller_plugin'][key] = 0.2
            _L().info('DropBot is not connected.  Set duration to 0.2 seconds '
                      '(temporarily) to mimic DropBot threshold actuation.')

        app_values = self.get_app_values()
        if app_values['c_liquid'] > 0:
            plugin_kwargs[self.name]['c_unit_area'] = app_values['c_liquid']

        @asyncio.coroutine
        def actuation_watcher(sender, **kwargs):
            if kwargs.get('capacitance_messages'):
                # Log capacitance update messages collected during actuation.
                # Notify volume threshold was reached through statusbar.
                capacitance_messages = kwargs['capacitance_messages']
                # Write capacitance updates to log in background thread.
                self.executor.submit(self.log_capacitance_updates,
                                     capacitance_messages)
            if 'threshold' in kwargs:
                # Notify volume threshold was reached through statusbar.

                # Compute area in units of m^2.
                meters_squared_area = kwargs['actuated_area'] * (1e-3 ** 2)
                # Approximate length of unit side in SI units.
                si_length, pow10 = si.split(np.sqrt(meters_squared_area))
                si_unit = si.SI_PREFIX_UNITS[len(si.SI_PREFIX_UNITS) // 2 +
                                             pow10 // 3]
                status = ('reached %sF (> %sF) over electrodes: %s (%.1f '
                          '%sm^2) after %ss' %
                          (si.si_format(kwargs['threshold']['measured']),
                           si.si_format(kwargs['threshold']['target']),
                           kwargs['actuated_channels'], si_length ** 2,
                           si_unit, (kwargs['threshold']['end'] -
                                     kwargs['threshold']['start'])
                           .total_seconds()))
                self.push_status(status)

        signals.signal('actuation-completed').connect(actuation_watcher,
                                                      weak=False)

        result = yield asyncio.From(execute(proxy, dmf_device, plugin_kwargs,
                                            signals))
        raise asyncio.Return(result)

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

        self.control_board.voltage = voltage

    @require_connection(log_level='info')  # Log if DropBot is not connected.
    def set_frequency(self, frequency):
        """
        Set the waveform frequency.

        Parameters:
            frequency : frequency in Hz
        """
        _L().debug("%.1f", frequency)
        self.control_board.frequency = frequency

    @require_connection(log_level='info')  # Log if DropBot is not connected.
    def on_experiment_log_changed(self, log):
        '''
        Add control board metadata to the experiment log.

        .. versionchanged:: 0.16.1
            Only attempt to run diagnostic tests if DropBot hardware is
            connected.

        .. versionchanged:: 2.35
            - Only run entire method if DropBot hardware is connected.
            - Display progress in a dialog while running diagnostic tests and
              allow user to cancel (logging test results for any completed
              tests).
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
        log.add_data(data)

        # add metadata to experiment log
        log.metadata[self.name] = data

        # run diagnostic tests
        app_values = self.get_app_values()
        if app_values.get('Auto-run diagnostic tests'):
            _L().info('Running diagnostic tests')
            tests = ['system_info',
                     'test_i2c',
                     'test_voltage',
                     'test_shorts',
                     'test_on_board_feedback_calibration']
            future = self.run_tests(tests)
            # XXX Execute pending GTK events to update progress dialog until
            # tests are completed.
            while not future.done():
                while gtk.events_pending():
                    gtk.main_iteration_do(block=False)
                time.sleep(.01)
        self._use_cached_capacitance_prompt()

    @require_connection()  # Display error dialog if DropBot is not connected.
    def run_tests(self, tests=None):
        '''
        .. versionadded:: 2.35

        Execute DropBot self-tests while display progress in a dialog.

        Allow user to cancel (logging test results for any completed tests).

        Parameters
        ----------
        tests : list, optional
            List of DropBot self-tests to run (e.g., ``'system_info'``,
            ``'test_i2c'``, etc.).  By default, run _all_ tests.

        Returns
        -------
        concurrent.futures.Future
            Asynchronous results of tests.  The `result()` method may be used
            to block until tests are complete, **_but_** **MUST** not be called
            from the GTK main thread, since doing so would prevent the progress
            dialog from displaying/updating.
        '''
        if tests is None:
            tests = db.self_test.ALL_TESTS

        signals = blinker.Namespace()

        @asyncio.coroutine
        def _run_tests():
            results = {}

            try:
                for i, test in enumerate(tests):
                    test_func = getattr(db.hardware_test, test)
                    signals.signal('test-started')\
                        .send({'test': test, 'completed': i,
                               'total': len(tests)})
                    results[test] = test_func(self.control_board)
                    signals.signal('test-completed')\
                        .send({'test': test, 'completed': i + 1,
                                'total': len(tests), 'results': results})
                    # Yield control to asyncio event loop.  This provides
                    # breakpoints where the coroutine may be cancelled.
                    yield asyncio.From(asyncio.sleep(0))
            except asyncio.CancelledError:
                # Gracefully exit if task is cancelled, returning results of
                # completed tests.
                pass
            finally:
                if results:
                    # Log results of completed tests.
                    db.hardware_test.log_results(results,
                                                 self.diagnostics_results_dir)
                    _L().info('Logged results to: `%s`',
                              self.diagnostics_results_dir.realpath())
            raise asyncio.Return(results)

        task = cancellable(_run_tests)
        # Write capacitance updates to log in background thread.
        future = self.executor.submit(task)

        @gtk_threadsafe
        def _show_progress_dialog():
            app = get_app()
            parent = app.main_window_controller.view
            dialog = gtk.MessageDialog(buttons=gtk.BUTTONS_CANCEL,
                                       flags=gtk.DIALOG_MODAL |
                                       gtk.DIALOG_DESTROY_WITH_PARENT,
                                       parent=parent)
            dialog.set_icon(parent.get_icon())
            dialog.set_title('DropBot self tests')
            dialog.props.text = 'Running DropBot diagnostic self tests.'
            dialog.props.destroy_with_parent = True
            dialog.props.window_position = gtk.WIN_POS_MOUSE
            # Disable `X` window close button.
            dialog.props.deletable = False
            content_area = dialog.get_content_area()
            progress = gtk.ProgressBar()
            content_area.pack_start(progress, fill=True, expand=True, padding=5)
            content_area.show_all()
            cancel_button = dialog.get_action_area().get_children()[0]

            # Close dialog once tests have completed.
            future.add_done_callback(lambda *args:
                                    gtk_threadsafe(dialog.destroy)())

            @gtk_threadsafe
            def _on_test_started(message):
                # Update progress bar.
                progress.set_fraction(message['completed'] / message['total'])
                progress.set_text('Running: `%s`' % message['test'])

            @gtk_threadsafe
            def _on_test_completed(message):
                # Update progress bar.
                progress.set_fraction(message['completed'] / message['total'])
                progress.set_text('Finished: `%s`' % message['test'])

            signals.signal('test-started').connect(_on_test_started)
            signals.signal('test-completed').connect(_on_test_completed)

            # Launch dialog to show test activity and wait until test has
            # completed.
            response = dialog.run()
            if response in (gtk.RESPONSE_DELETE_EVENT, gtk.RESPONSE_CANCEL):
                # User clicked cancel button.  Cancel remaining tests.
                task.cancel()
                if not future.done():
                    cancel_button.props.label = 'Cancelling...'
                    cancel_button.props.sensitive = False

        _show_progress_dialog()
        return future

    @gtk_threadsafe
    @require_connection(log_level='info')  # Log if DropBot is not connected.
    def _use_cached_capacitance_prompt(self):
        '''
        .. versionadded:: 0.18

        .. versionchanged:: 2.35
            Only run if DropBot is connected.
        '''
        # XXX TODO add event to indicate if `c_liquid` has been confirmed; either by prompting to use cached value or by measuring new value.
        # XXX TODO add event to indicate if `c_filler` has been confirmed; either by prompting to use cached value or by measuring new value.
        app_values = self.get_app_values()
        if app_values['c_liquid'] > 0 or app_values['c_filler'] > 0:
            response = yesno('Use cached value for c<sub>liquid</sub> '
                             'and c<sub>filler</sub>?')
            # reset the cached capacitance values
            if response == gtk.RESPONSE_NO:
                self.set_app_values(dict(c_liquid=0, c_filler=0))

    def get_schedule_requests(self, function_name):
        """
        Returns a list of scheduling requests (i.e., ScheduleRequest
        instances) for the function specified by function_name.


        .. versionadded:: 2.34
            Enable _after_ command plugin and zmq hub to ensure command can be
            registered.
        '''
        """
        if function_name == 'on_app_options_changed':
            return [ScheduleRequest('microdrop.app', self.name)]
        elif function_name == 'on_protocol_swapped':
            return [ScheduleRequest('microdrop.gui.protocol_grid_controller',
                                    self.name)]
        elif function_name == 'on_app_exit':
            return [ScheduleRequest('microdrop.gui.experiment_log_controller',
                                    self.name)]
        elif function_name == 'on_plugin_enable':
            return [ScheduleRequest(p, self.name)
                    for p in ('microdrop.zmq_hub_plugin',
                              'microdrop.command_plugin')]
        return []

    def find_liquid(self):
        '''
        .. versionadded:: 2.36

        Turn on electrodes where capacitance level suggests liquid is present.
        '''
        app = get_app()
        channels = app.dmf_device.channel_areas[app.dmf_device.channel_areas >
                                                0].index.drop_duplicates()
        capacitances = pd.Series(self.control_board
                                 .channel_capacitances(channels),
                                 index=channels)
        capacitances = capacitances[capacitances > 0]
        if capacitances.shape[0] < 1:
            return
        liquid_channels = capacitances[capacitances > 10 * capacitances.min()]
        map(_L().info, str(capacitances.describe()).splitlines())
        if liquid_channels.shape[0] > .5 * channels.shape[0]:
            # More than half of the channels identified as containing liquid...
            # Assume threshold is incorrect.
            return
        liquid_channels.sort_index(inplace=True)
        liquid_electrodes = \
            app.dmf_device.electrodes_by_channel.loc[liquid_channels.index]
        hub_execute('microdrop.electrode_controller_plugin',
                    'set_electrode_states',
                    electrode_states=pd.Series(1, index=liquid_electrodes))
        return liquid_electrodes.values

    def identify_electrode(self, electrode_id):
        '''
        .. versionadded:: 2.36

        Pulse each neighbour electrode to help visually identify an electrode.
        '''
        app = get_app()
        neighbours = app.dmf_device.electrode_neighbours.loc[electrode_id].dropna()
        neighbour_channels = \
            app.dmf_device.channels_by_electrode.loc[neighbours]

        for channel in neighbour_channels:
            for state in (1, 0):
                self.control_board.state_of_channels = \
                    pd.Series(state, index=[channel])

    def on_mode_changed(self, old_mode, new_mode):
        '''
        .. versionadded:: 2.37
        '''
        if (all([(old_mode & MODE_REAL_TIME_MASK),
                 (new_mode & ~MODE_REAL_TIME_MASK),
                 (new_mode & ~MODE_RUNNING_MASK)]) or
            all([(old_mode & MODE_RUNNING_MASK),
                 (new_mode & ~MODE_RUNNING_MASK)])):
            # Either real-time mode was disabled when it was enabled or
            # protocol just stopped running.
            self.turn_off()

PluginGlobals.pop_env()
