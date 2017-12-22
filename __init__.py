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
from functools import wraps
import datetime as dt
import json
import logging
import pkg_resources
import re
import threading
import types
import warnings
import webbrowser

from dropbot import SerialProxy
from flatland import Integer, Float, Form, Enum, Boolean
from flatland.validation import ValueAtLeast, ValueAtMost
from matplotlib.backends.backend_gtkagg import (FigureCanvasGTKAgg as
                                                FigureCanvas)
from matplotlib.figure import Figure
from matplotlib import mlab
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
from serial_device import get_serial_ports
from zmq_plugin.plugin import Plugin as ZmqPlugin
from zmq_plugin.schema import decode_content_data
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
import microdrop_utility as utility
import numpy as np
import pandas as pd
import path_helpers as ph
import tables
import zmq

from ._version import get_versions
from .noconflict import classmaker
__version__ = get_versions()['version']
del get_versions
from .noconflict import classmaker

# Prevent warning about potential future changes to Numpy scalar encoding
# behaviour.
json_tricks.NumpyEncoder.SHOW_SCALAR_WARNING = False

logger = logging.getLogger(__name__)


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
                    self.parent.actuated_area = data['actuated_area']
                    self.parent.update_channel_states(data['channel_states'])
                elif msg['content']['command'] == 'get_channel_states':
                    data = decode_content_data(msg)
                    self.parent.actuated_area = data['actuated_area']
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
            logger.error('Error processing message from subscription '
                         'socket.', exc_info=True)
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


def require_connection(func):
    '''
    Decorator to require DropBot connection.
    '''
    @wraps(func)
    def _wrapped(self, *args, **kwargs):
        if not self.dropbot_connected.is_set():
            logger.error('DropBot is not connected.')
        else:
            return func(self, *args, **kwargs)
    return _wrapped


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
    '''
    @wraps(func)
    def _wrapped(*args, **kwargs):
        plugin_dir = ph.path(__file__).realpath().parent
        images_dir = plugin_dir.joinpath('images', 'insert_test_board')
        image_paths = sorted(images_dir.files('insert_test_board-*.jpg'))
        dialog = animation_dialog(image_paths, loop=True,
                                  buttons=gtk.BUTTONS_OK_CANCEL)
        dialog.props.text = ('<b>Please insert the DropBot test board</b>\n\n'
                             'For more info, see: https://goo.gl/9uHGNW')
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
    """
    # Without the follow line, cannot inherit from both `Plugin` and
    # `gobject.GObject`.  See [here][1] for more details.
    #
    # [1]: http://code.activestate.com/recipes/204197-solving-the-metaclass-conflict/
    __metaclass__ = classmaker()

    gsignal('dropbot-connected', object)
    gsignal('dropbot-disconnected')

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
        self._dropbot_connected = threading.Event()

        def _on_dropbot_connected(*args):
            self.dropbot_connected.set()
            self.update_connection_status()

        self.connect('dropbot-connected', _on_dropbot_connected)

        def _on_dropbot_disconnected(*args):
            self.dropbot_connected.clear()
            self.update_connection_status()

        self.connect('dropbot-disconnected', _on_dropbot_disconnected)

    @property
    def dropbot_connected(self):
        '''
        Event set when DropBot is connected (and cleared when DropBot is
        disconnected).
        '''
        return self._dropbot_connected

    @gtk_threadsafe  # Execute in GTK main thread
    @error_ignore(lambda exception, func, self, test_name, *args:
                  logger.error('Error executing: "%s"', test_name,
                               exc_info=True))
    @require_connection  # Display error dialog if DropBot is not connected.
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
        map(logger.info, map(unicode.rstrip, unicode(message).splitlines()))

        app = get_app()
        parent = app.main_window_controller.view
        dialog = results_dialog(test_name, results, parent=parent,
                                axis_count=axis_count)
        dialog.run()
        dialog.destroy()

    @gtk_threadsafe  # Execute in GTK main thread
    @error_ignore(lambda *args:
                  logger.error('Error executing DropBot self tests.',
                               exc_info=True))
    @require_connection  # Display error dialog if DropBot is not connected.
    @require_test_board  # Prompt user to insert DropBot test board
    def run_all_tests(self):
        '''
        Run all DropBot on-board self-diagnostic tests.

        Record test results as JSON and results summary as a Word document.

        .. versionadded:: 0.14

        .. versionchanged:: 0.16
            Prompt user to insert DropBot test board.
        '''
        results = db.self_test.self_test(self.control_board)
        results_dir = ph.path(self.diagnostics_results_dir)
        results_dir.makedirs_p()

        # Create unique output filenames based on current timestamp.
        timestamp = dt.datetime.now().isoformat().replace(':', '_')
        json_path = results_dir.joinpath('results-%s.json' % timestamp)
        report_path = results_dir.joinpath('results-%s.docx' % timestamp)

        # Write test results encoded as JSON.
        with json_path.open('w') as output:
            # XXX Use `json_tricks` rather than standard `json` to support
            # serializing [Numpy arrays and scalars][1].
            #
            # [1]: http://json-tricks.readthedocs.io/en/latest/#numpy-arrays
            output.write(json_tricks.dumps(results, indent=4))

        # Generate test result summary report as Word document.
        db.self_test.generate_report(results, output_path=report_path,
                                     force=True)
        # Launch Word document report.
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
        serial_ports = list(get_serial_ports())
        if len(serial_ports):
            default_port = serial_ports[0]
        else:
            default_port = None

        return Form.of(
            Enum.named('serial_port')
            .using(default=default_port, optional=True).valued(*serial_ports),
            Float.named('default_duration').using(default=1000, optional=True),
            Float.named('default_voltage').using(default=80, optional=True),
            Float.named('default_frequency').using(default=10e3,
                                                   optional=True),
            Boolean.named('Auto-run diagnostic tests').using(default=True,
                                                             optional=True),
            # .. versionadded: 0.18
            Float.named('c_liquid').using(default=0, optional=True,
                                          properties={'show_in_gui': False}),
            # .. versionadded: 0.18
            Float.named('c_filler').using(default=0, optional=True,
                                          properties={'show_in_gui': False}))

    def get_step_form_class(self):
        """
        Override to set default values based on their corresponding app options.
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
                       # .. versionadded: 0.18
                       Float.named('volume_threshold')
                       .using(default=0,
                              optional=True,
                              validators=[ValueAtLeast(minimum=0),
                                          ValueAtMost(maximum=1.0)]),
                       # .. versionadded: 0.18
                       Integer.named('max_repeats')
                       .using(default=3,
                              optional=True,
                              validators=[ValueAtLeast(minimum=0)]))

    def update_channel_states(self, channel_states):
        logging.info('update_channel_states')
        # Update locally cached channel states with new modified states.
        try:
            self.channel_states = channel_states.combine_first(self
                                                               .channel_states)
        except ValueError:
            logging.info('channel_states: %s', channel_states)
            logging.info('self.channel_states: %s', self.channel_states)
            logging.info('', exc_info=True)
        else:
            app = get_app()
            connected = self.control_board is not None
            if connected and (app.realtime_mode or app.running):
                self.on_step_run()

    def cleanup_plugin(self):
        if self.plugin_timeout_id is not None:
            gobject.source_remove(self.plugin_timeout_id)
        if self.plugin is not None:
            self.plugin = None
        if self.control_board is not None:
            self.control_board.hv_output_enabled = False
            self.control_board.terminate()
            self.control_board = None
            gobject.idle_add(self.emit, 'dropbot-disconnected')

    def on_plugin_enable(self):
        super(DropBotPlugin, self).on_plugin_enable()
        if not self.menu_items:
            # Schedule initialization of menu user interface.  Calling
            # `create_ui()` directly is not thread-safe, since it includes GTK
            # code.
            gobject.idle_add(self.create_ui)

        self.cleanup_plugin()
        # Initialize 0MQ hub plugin and subscribe to hub messages.
        self.plugin = DmfZmqPlugin(self, self.name, get_hub_uri(),
                                   subscribe_options={zmq.SUBSCRIBE: ''})
        # Initialize sockets.
        self.plugin.reset()

        # Periodically process outstanding message received on plugin sockets.
        self.plugin_timeout_id = gtk.timeout_add(10, self.plugin.check_sockets)

        self.check_device_name_and_version()
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
        app = get_app()
        if plugin_name == self.name:
            app_values = self.get_app_values()
            reconnect = False

            if self.control_board:
                for k, v in app_values.items():
                    if k == 'serial_port' and self.control_board.port != v:
                        reconnect = True

            if reconnect:
                self.connect_dropbot()

            self._update_protocol_grid()
        elif plugin_name == app.name:
            # Turn off all electrodes if we're not in realtime mode and not
            # running a protocol.
            if self.control_board and (not app.realtime_mode and
                                       not app.running):
                logger.info('Turning off all electrodes.')
                self.control_board.hv_output_enabled = False

    def connect_dropbot(self):
        """
        Try to connect to the control board at the default serial port selected
        in the Microdrop application options.

        If unsuccessful, try to connect to the control board on any available
        serial port, one-by-one.
        """
        if self.control_board:
            self.control_board.terminate()
            self.control_board = None
            gobject.idle_add(self.emit, 'dropbot-disconnected')
        self.current_frequency = None
        serial_ports = list(get_serial_ports())
        if serial_ports:
            app_values = self.get_app_values()
            # try to connect to the last successful port
            try:
                port = app_values.get('serial_port')
                self.control_board = SerialProxy(port=port)
            except Exception:
                logger.warning('Could not connect to control board on port %s.'
                               ' Checking other ports...',
                               app_values['serial_port'], exc_info=True)
                self.control_board = SerialProxy()
            self.control_board.initialize_switching_boards()
            app_values['serial_port'] = self.control_board.port
            self.set_app_values(app_values)
            gobject.idle_add(self.emit, 'dropbot-connected',
                             self.control_board)
        else:
            raise Exception("No serial ports available.")

    def data_dir(self):
        '''
        .. versionadded: 0.18
        '''
        app = get_app()
        data_dir = app.experiment_log.get_log_path().joinpath(self.name)
        if not data_dir.isdir():
            data_dir.makedirs_p()
        return data_dir

    def check_device_name_and_version(self):
        """
        Check to see if:

         a) The connected device is a DropBot
         b) The device firmware matches the host driver API version

        In the case where the device firmware version does not match, display a
        dialog offering to flash the device with the firmware version that
        matches the host driver API version.
        """
        try:
            self.connect_dropbot()
            name = self.control_board.properties['package_name']
            if name != self.control_board.host_package_name:
                raise Exception("Device is not a DropBot")

            host_software_version = utility.Version.fromstring(
                str(self.control_board.host_software_version))
            remote_software_version = utility.Version.fromstring(
                str(self.control_board.remote_software_version))

            @gtk_threadsafe
            def _firmware_check():
                # Offer to reflash the firmware if the major and minor versions
                # are not not identical. If micro versions are different, the
                # firmware is assumed to be compatible. See [1]
                #
                # [1]: https://github.com/wheeler-microfluidics/base-node-rpc/issues/8
                if any([host_software_version.major !=
                        remote_software_version.major,
                        host_software_version.minor !=
                        remote_software_version.minor]):
                    response = yesno("The DropBot firmware version (%s) does "
                                     "not match the driver version (%s). "
                                     "Update firmware?" %
                                     (remote_software_version,
                                      host_software_version))
                    if response == gtk.RESPONSE_YES:
                        self.on_flash_firmware()

            # Call as thread-safe function, since function uses GTK.
            _firmware_check()
        except pkg_resources.DistributionNotFound:
            logger.debug('No distribution found for `%s`.  This may occur if, '
                         'e.g., `%s` is installed using `conda develop .`',
                         name, name, exc_info=True)
        except Exception, why:
            logger.warning("%s" % why)

    def on_flash_firmware(self, widget=None, data=None):
        app = get_app()
        try:
            connected = self.control_board is not None
            if not connected:
                self.connect_dropbot()
            self.control_board.flash_firmware()
            app.main_window_controller.info("Firmware updated successfully.",
                                            "Firmware update")
        except Exception, why:
            logger.error("Problem flashing firmware. ""%s" % why)
        self.check_device_name_and_version()

    def update_connection_status(self):
        '''
        Update connection status message and corresponding UI label.

        .. versionchanged:: 0.14
            Schedule update of control board status label in main GTK thread.

        .. versionchanged:: 0.18
            Toggle sensitivity of DropBot control board menu items based on
            control board connection status.
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
                                      '%s)\n' '%d channels' %
                                      (properties['display_name'], version,
                                       properties['software_version'], id,
                                       str(uuid)[:8], n_channels))

        @gtk_threadsafe
        def _update_ui_connected_status():
            # Enable/disable control board menu items based on the connection
            # status of the control board.
            for menu_item_i in self.menu_items:
                menu_item_i.set_sensitive(self.dropbot_connected.is_set())

            app.main_window_controller.label_control_board_status\
                .set_text(self.connection_status)
        _update_ui_connected_status()

    def measure_capacitance(self):
        '''
        Measure the capacitance of all actuated electrodes on the device
        and send an 'on_device_capacitance_update' signal to update to
        any listeners.

        .. versionadded: 0.18
        '''
        c = self.control_board.measure_capacitance()
        v = self.control_board.measure_voltage()
        results = {'capacitance': c,
                   'voltage': v}
        # send a signal to update the gui
        emit_signal('on_device_capacitance_update', results)
        return dict(capacitance=c, voltage=v)

    def on_device_capacitance_update(self, results):
        '''
        .. versionadded: 0.18
        '''
        area = self.actuated_area
        voltage = results['voltage']
        capacitance = results['capacitance']

        app = get_app()
        app_values = self.get_app_values()
        c_liquid = app_values['c_liquid']

        label = 'Voltage: %.1f V, Capacitance: %.1f pF' % (voltage, 1e12 *
                                                           capacitance)

        # add normalized force to the label if we've calibrated the device
        if c_liquid > 0:
            # TODO: calculate force including filler media
            label += (u'\nForce: %.1f \u03BCN/mm (c<sub>device</sub>='
                      u'%.1f pF/mm<sup>2</sup>)' % (1e9 * 0.5 * c_liquid *
                                                    voltage**2, 1e12 *
                                                    c_liquid))

        # Schedule update of control board status label in main GTK thread.
        gobject.idle_add(app.main_window_controller.label_control_board_status
                         .set_text, ', '.join([self.connection_status, label]))

        options = self.get_step_options()
        logger.info('on_device_capacitance_update():')
        logger.info('\tset_voltage=%.1f, measured_voltage=%.1f, '
                    'error=%.1f%%', options['voltage'], voltage,
                    100 * (voltage - options['voltage']) / options['voltage'])

        # TODO: check that the voltage is within tolerance

        # Append data to CSV file.
        csv_output_path = self.data_dir().joinpath('data.csv')
        # Only include header if the file does not exist or is empty.
        include_header = not (csv_output_path.isfile() and
                              (csv_output_path.size > 0))

        df = pd.DataFrame(dict(
            utc_timestamp=[dt.datetime.utcnow()],
            area=[area],
            step=[app.protocol.current_step_number + 1],
            attempt=[app.protocol.current_step_attempt],
            voltage=[voltage],
            capacitance=[capacitance],
            channels=[mlab.find(self.control_board.state_of_channels).tolist()]))

        with csv_output_path.open('a') as output:
            df.to_csv(output, index=False,
                      header=include_header)

    def _calibrate_device_capacitance(self, name):
        '''
        .. versionadded: 0.18
        '''
        a = self.actuated_area
        if self.control_board is None:
            logger.error('DropBot is not connected.')
        elif a == 0:
            logger.error('At least one electrode must be actuated to perform '
                         'calibration.')
        else:
            max_channels = self.control_board.number_of_channels
            # All channels should default to off.
            channel_states = np.zeros(max_channels, dtype=int)
            # Set the state of any channels that have been set explicitly.
            channel_states[self.channel_states.index
                           .values.tolist()] = self.channel_states

            # set the voltage and frequency specified for the current step
            options = self.get_step_options()
            emit_signal("set_frequency",
                        options['frequency'],
                        interface=IWaveformGenerator)
            emit_signal("set_voltage", options['voltage'],
                        interface=IWaveformGenerator)

            # enable high voltage
            if not self.control_board.hv_output_enabled:
                self.control_board.hv_output_enabled = True

            # perform the capacitance measurement
            self.control_board.set_state_of_channels(channel_states)
            c = self.control_board.measure_capacitance()
            logger.info("on_measure_%s_capacitance: "
                        "%.1f pF/%.1f mm^2 = %.1f pF/mm^2" % (name, c * 1e12,
                                                              a, c / a * 1e12))
            app_values = {}
            app_values['c_%s' % name] = c / a
            self.set_app_values(app_values)

            v = self.control_board.measure_voltage()
            results = {'capacitance': c,
                       'voltage': v}
            # send a signal to update the gui
            emit_signal('on_device_capacitance_update', results)

            # Turn off all electrodes and disable high voltage if we're
            # not in realtime mode.
            if not get_app().realtime_mode:
                self.control_board.hv_output_enabled = False
                self.control_board.set_state_of_channels(
                    np.zeros(max_channels, dtype=int))

    def on_measure_liquid_capacitance(self):
        '''
        .. versionadded: 0.18
        '''
        self._calibrate_device_capacitance('liquid')

    def on_measure_filler_capacitance(self):
        '''
        .. versionadded: 0.18
        '''
        self._calibrate_device_capacitance('filler')

    def on_step_run(self):
        """
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
        """
        logger.debug('[DropBotPlugin] on_step_run()')
        self._kill_running_step()
        app = get_app()
        options = self.get_step_options()

        if (self.control_board and (app.realtime_mode or app.running)):
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
                self.control_board.hv_output_enabled = True

            self.control_board.set_state_of_channels(channel_states)

            # If the app is not running, we must be in realtime mode.
            # Measure the voltage and capacitance and update the gui.
            if not app.running:
                self.measure_capacitance()

        # if a protocol is running, wait for the specified minimum duration
        if app.running:
            logger.debug('[DropBotPlugin] on_step_run: '
                         'timeout_add(%d, _callback_step_completed)' %
                         options['duration'])
            self.timeout_id = gobject.timeout_add(
                options['duration'], self._callback_step_completed)
            return
        else:
            self.step_complete()

    def step_complete(self, return_value=None):
        app = get_app()
        if app.running or app.realtime_mode:
            emit_signal('on_step_complete', [self.name, return_value])

    def on_step_complete(self, plugin_name, return_value=None):
        if plugin_name == self.name:
            self.timeout_id = None

    def _kill_running_step(self):
        if self.timeout_id:
            logger.debug('[DropBotPlugin] _kill_running_step: removing'
                         'timeout_id=%d' % self.timeout_id)
            gobject.source_remove(self.timeout_id)

    def _callback_step_completed(self):
        results = self.measure_capacitance()
        c = results['capacitance']

        app = get_app()

        app_values = self.get_app_values()
        c_liquid = app_values['c_liquid']

        step_options = self.get_step_options()
        volume_threshold = step_options['volume_threshold']
        max_repeats = step_options['max_repeats']

        a = self.actuated_area
        return_value = None
        info_msg = ('_callback_step_completed: attempt=%d' %
                    app.protocol.current_step_attempt)

        # if a volume threshold has been set for this step, check if the
        # normalized capacitance exceeds the threshold
        if volume_threshold > 0 and a > 0 and c_liquid > 0:
            normalized_capacitance = c / a
            info_msg += ', C/A=%.1f pF/mm^2' % (1e12 * normalized_capacitance)

            # if the measured capacitance is not above the threshold
            if normalized_capacitance < volume_threshold * c_liquid:
                # if we're at the max number of repeats, fail; otherwise,
                # repeat the step
                if app.protocol.current_step_attempt == max_repeats:
                    return_value = 'Fail'
                else:
                    return_value = 'Repeat'

        if return_value:
            info_msg += '. %s' % return_value
        else:
            info_msg += '. OK'

        logger.info(info_msg)
        self.step_complete(return_value)
        return False  # stop the timeout from refiring

    def on_protocol_run(self):
        """
        Handler called when a protocol starts running.
        """
        app = get_app()
        if not self.control_board:
            logger.warning("Warning: no control board connected.")
        elif (self.control_board.number_of_channels <=
              app.dmf_device.max_channel()):
            logger.warning("Warning: currently connected board does not have "
                           "enough channels for this protocol.")

    def on_protocol_pause(self):
        """
        Handler called when a protocol is paused.
        """
        app = get_app()
        self._kill_running_step()
        if self.control_board and not app.realtime_mode:
            # Turn off all electrodes
            logger.debug('Turning off all electrodes.')
            self.control_board.hv_output_enabled = False

    def on_experiment_log_selection_changed(self, data):
        """
        Handler called whenever the experiment log selection changes.

        Parameters:
            data : dictionary of experiment log data for the selected steps
        """
        pass

    def set_voltage(self, voltage):
        """
        Set the waveform voltage.

        Parameters:
            voltage : RMS voltage
        """
        logger.info("set_voltage(%.1f)" % voltage)
        self.control_board.voltage = voltage

    def set_frequency(self, frequency):
        """
        Set the waveform frequency.

        Parameters:
            frequency : frequency in Hz
        """
        logger.info("set_frequency(%.1f)" % frequency)
        self.control_board.frequency = frequency
        self.current_frequency = frequency

    def on_step_options_changed(self, plugin, step_number):
        logger.info('on_step_options_changed(): %s step #%d',
                    plugin, step_number)
        app = get_app()
        if (app.protocol and not app.running and not app.realtime_mode and
            (plugin == 'microdrop.gui.dmf_device_controller' or plugin ==
             self.name) and app.protocol.current_step_number == step_number):
            self.on_step_run()

    def on_step_swapped(self, original_step_number, new_step_number):
        logger.info('on_step_swapped():'
                    'original_step_number=%d, new_step_number=%d',
                    original_step_number, new_step_number)
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
            logger.info('Running diagnostic tests')
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
            logger.info('DropBot not connected - not running diagnostic tests')

        self._use_cached_capacitance_prompt()

    @gtk_threadsafe
    def _use_cached_capacitance_prompt(self):
        '''
        .. versionadded: 0.18
        '''
        app_values = self.get_app_values()
        if (self.control_board and (app_values['c_liquid'] > 0 or
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
