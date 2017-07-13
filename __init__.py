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
import json
import logging
import pkg_resources
import warnings

from dropbot import SerialProxy
from flatland import Integer, Float, Form, Enum
from flatland.validation import ValueAtLeast
from microdrop.app_context import get_app, get_hub_uri
from microdrop.gui.protocol_grid_controller import ProtocolGridController
from microdrop.plugin_helpers import (StepOptionsController, AppDataController)
from microdrop.plugin_manager import (IPlugin, IWaveformGenerator, Plugin,
                                      implements, PluginGlobals,
                                      ScheduleRequest, emit_signal,
                                      get_service_instance,
                                      get_service_instance_by_name)
from microdrop_utility.gui import yesno
from serial_device import get_serial_ports
from zmq_plugin.plugin import Plugin as ZmqPlugin
from zmq_plugin.schema import decode_content_data
import conda_helpers as ch
import dropbot as db
import dropbot.hardware_test
import gobject
import gtk
import microdrop_utility as utility
import numpy as np
import pandas as pd
import path_helpers as ph
import tables
import zmq

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
            if ((source == 'microdrop.electrode_controller_plugin') and
                (msg_type == 'execute_reply')):
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
                    self.parent.channel_states = self.parent.channel_states.iloc[0:0]
                    self.parent.update_channel_states(data['channel_states'])
            else:
                self.most_recent = msg_json
        except zmq.Again:
            pass
        except:
            logger.error('Error processing message from subscription '
                         'socket.', exc_info=True)
        return True


def max_voltage(element, state):
    """Verify that the voltage is below a set maximum"""
    service = get_service_instance_by_name(ph.path(__file__).parent.name)

    if service.control_board and \
        element.value > service.control_board.max_waveform_voltage:
        return element.errors.append('Voltage exceeds the maximum value '
                                     '(%d V).' %
                                     service.control_board.max_waveform_voltage)
    else:
        return True


def check_frequency(element, state):
    """Verify that the frequency is within the valid range"""
    service = get_service_instance_by_name(ph.path(__file__).parent.name)

    if service.control_board and \
        (element.value < service.control_board.min_waveform_frequency or \
        element.value > service.control_board.max_waveform_frequency):
        return element.errors.append('Frequency is outside of the valid range '
            '(%.1f - %.1f Hz).' %
            (service.control_board.min_waveform_frequency,
             service.control_board.max_waveform_frequency)
        )
    else:
        return True


class DropBotPlugin(Plugin, StepOptionsController, AppDataController):
    """
    This class is automatically registered with the PluginManager.
    """
    implements(IPlugin)
    implements(IWaveformGenerator)

    plugin_name = ph.path(__file__).realpath().parent.name
    try:
        version = ch.package_version(plugin_name).get('version')
    except NameError:
        version = None

    @property
    def StepFields(self):
        """
        Expose StepFields as a property to avoid breaking code that accesses
        the StepFields member (vs through the get_step_form_class method).
        """
        return self.get_step_form_class()


    def __init__(self):
        self.control_board = None
        self.name = self.plugin_name
        self.connection_status = "Not connected"
        self.current_frequency = None
        self.timeout_id = None
        self.channel_states = pd.Series()
        self.plugin = None
        self.plugin_timeout_id = None
        self.menu_items = []

    def create_ui(self):
        '''
        Create user interface elements (e.g., menu items).
        '''
        def _test_high_voltage(*args):
            if self.control_board is None:
                logger.error('DropBot is not connected.')
            else:
                try:
                    mean_rms_error = db.hardware_test(self.control_board)
                    logger.info('High-voltage error: %.2f%%', mean_rms_error)

                    if mean_rms_error < .5:
                        # Display dialog indicating RMS voltage error.
                        dialog = gtk.MessageDialog(buttons=gtk.BUTTONS_OK)
                        dialog.set_title('High-voltage test passed')
                        dialog.props.text = ('High-voltage average RMS: '
                                             '{:.2f}%', mean_rms_error * 100)
                        dialog.run()
                        dialog.destroy()
                    else:
                        logger.warning('High-voltage average RMS: %2f%%',
                                       mean_rms_error * 100)
                except:
                    logger.error('Error executing high voltage test.',
                                 exc_info=True)

        def _test_shorts(*args):
            if self.control_board is None:
                logger.error('DropBot is not connected.')
            else:
                try:
                    shorts = db.detect_shorted_channels(self.control_board)

                    if shorts:
                        # Display dialog indicating RMS voltage error.
                        dialog = gtk.MessageDialog(buttons=gtk.BUTTONS_OK)
                        dialog.set_title('No shorts detected')
                        dialog.props.text = 'No shorts were detected on chip.'
                        dialog.run()
                        dialog.destroy()
                    else:
                        logger.warning('Shorts were detected on the following '
                                       'channels: %s', ', '.join(map(str,
                                                                     shorts)))
                except:
                    logger.error('Error executing short detection test.',
                                 exc_info=True)

        self.menu_items = [gtk.MenuItem('Test high voltage'),
                           gtk.MenuItem('Detect shorted channels')]
        self.menu_items[0].connect('activate', _test_high_voltage)
        self.menu_items[1].connect('activate', _test_shorts)

        app = get_app()
        for menu_item_i in self.menu_items:
            app.main_window_controller.menu_tools.append(menu_item_i)
            menu_item_i.show()

    @property
    def AppFields(self):
        serial_ports = list(get_serial_ports())
        if len(serial_ports):
            default_port = serial_ports[0]
        else:
            default_port = None

        return Form.of(
            Enum.named('serial_port').using(default=default_port,
                                            optional=True).valued(*serial_ports),
            Float.named('default_duration').using(default=1000, optional=True),
            Float.named('default_voltage').using(default=80, optional=True),
            Float.named('default_frequency').using(default=10e3,
                                                   optional=True))

    def get_step_form_class(self):
        """
        Override to set default values based on their corresponding app options.
        """
        app_values = self.get_app_values()
        return Form.of(
            Integer.named('duration').using(default=app_values['default_duration'],
                                            optional=True,
                                            validators=
                                            [ValueAtLeast(minimum=0), ]),
            Float.named('voltage').using(default=app_values['default_voltage'],
                                         optional=True,
                                         validators=[ValueAtLeast(minimum=0),
                                                     max_voltage]),
            Float.named('frequency').using(default=app_values['default_frequency'],
                                           optional=True,
                                           validators=[ValueAtLeast(minimum=0),
                                                       check_frequency]))

    def update_channel_states(self, channel_states):
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
            connected = self.control_board != None
            if connected and (app.realtime_mode or app.running):
                self.on_step_run()

    def cleanup_plugin(self):
        if self.plugin_timeout_id is not None:
            gobject.source_remove(self.plugin_timeout_id)
        if self.plugin is not None:
            self.plugin = None
        if self.control_board is not None:
            # Disconnect
            del self.control_board
            self.control_board = None

    def on_plugin_enable(self):
        super(DropBotPlugin, self).on_plugin_enable()
        if not self.menu_items:
            # Initialize menu user interface.
            self.create_ui()

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
            self.control_board.hv_output_enabled = False
        except: # ignore any exceptions (e.g., if the board is not connected)
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
                self.connect()

            self._update_protocol_grid()
        elif plugin_name == app.name:
            # Turn off all electrodes if we're not in realtime mode and not
            # running a protocol.
            if (self.control_board and not app.realtime_mode and
                not app.running):
                logger.info('Turning off all electrodes.')
                self.control_board.hv_output_enabled = False

    def connect(self):
        """
        Try to connect to the control board at the default serial port selected
        in the Microdrop application options.

        If unsuccessful, try to connect to the control board on any available
        serial port, one-by-one.
        """
        self.current_frequency = None
        serial_ports = list(get_serial_ports())
        if serial_ports:
            app_values = self.get_app_values()
            # try to connect to the last successful port
            try:
                port = app_values.get('serial_port')
                self.control_board = SerialProxy(port=port)
            except:
                logger.warning('Could not connect to control board on port %s.'
                               ' Checking other ports...',
                               app_values['serial_port'], exc_info=True)
                self.control_board = SerialProxy()
            self.control_board.initialize_switching_boards()
            app_values['serial_port'] = self.control_board.port
            self.set_app_values(app_values)
        else:
            raise Exception("No serial ports available.")

    def check_device_name_and_version(self):
        """
        Check to see if:

         a) The connected device is a OpenDrop
         b) The device firmware matches the host driver API version

        In the case where the device firmware version does not match, display a
        dialog offering to flash the device with the firmware version that
        matches the host driver API version.
        """
        try:
            self.connect()
            name = self.control_board.properties['package_name']
            if name != self.control_board.host_package_name:
                raise Exception("Device is not a DropBot")

            host_software_version = self.control_board.host_software_version
            remote_software_version = self.control_board.remote_software_version

            # Reflash the firmware if it is not the right version.
            if host_software_version != remote_software_version:
                response = yesno("The DropBot firmware version (%s) "
                                 "does not match the driver version (%s). "
                                 "Update firmware?" % (remote_software_version,
                                                       host_software_version))
                if response == gtk.RESPONSE_YES:
                    self.on_flash_firmware()
        except pkg_resources.DistributionNotFound:
            logger.debug('No distribution found for `%s`.  This may occur if, '
                         'e.g., `%s` is installed using `conda develop .`',
                         name, name, exc_info=True)
        except Exception, why:
            logger.warning("%s" % why)

        self.update_connection_status()

    def on_flash_firmware(self, widget=None, data=None):
        app = get_app()
        try:
            connected = self.control_board != None
            if not connected:
                self.connect()
            """
            response = yesno("Save current control board configuration before "
                             "flashing?")
            if response == gtk.RESPONSE_YES:
                self.save_config()
            """
            hardware_version = utility.Version.fromstring(
                self.control_board.hardware_version
            )
            if connected:
                # disconnect
                del self.control_board
                self.control_board = None
            self.control_board.flash_firmware(hardware_version)
            app.main_window_controller.info("Firmware updated successfully.",
                                            "Firmware update")
        except Exception, why:
            logger.error("Problem flashing firmware. ""%s" % why)
        self.check_device_name_and_version()

    def update_connection_status(self):
        self.connection_status = "Not connected"
        app = get_app()
        connected = self.control_board != None
        if connected:
            properties = self.control_board.properties
            version = self.control_board.hardware_version
            n_channels = self.control_board.number_of_channels
            id = self.control_board.id
            uuid = self.control_board.uuid
            self.connection_status = ('%s v%s (Firmware: %s, id: %s, uuid: %s)\n'
                '%d channels' % (properties['display_name'], version,
                                 properties['software_version'], id, str(uuid)[:8],
                                 n_channels))

        app.main_window_controller.label_control_board_status\
           .set_text(self.connection_status)

    def on_step_run(self):
        """
        Handler called whenever a step is executed.

        Plugins that handle this signal must emit the on_step_complete
        signal once they have completed the step. The protocol controller
        will wait until all plugins have completed the current step before
        proceeding.
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

            label = (self.connection_status + ', Voltage: %.1f V' %
                 self.control_board.measured_voltage)
            app.main_window_controller.label_control_board_status. \
                set_markup(label)


            self.control_board.set_state_of_channels(channel_states)

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
        logger.debug('[DropBotPlugin] _callback_step_completed')
        self.step_complete()
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
        logger.info("[DropBotPlugin].set_voltage(%.1f)" % voltage)
        self.control_board.voltage = voltage

    def set_frequency(self, frequency):
        """
        Set the waveform frequency.

        Parameters:
            frequency : frequency in Hz
        """
        logger.info("[DropBotPlugin].set_frequency(%.1f)" % frequency)
        self.control_board.frequency = frequency
        self.current_frequency = frequency

    def on_step_options_changed(self, plugin, step_number):
        logger.debug('[DropBotPlugin] on_step_options_changed(): %s '
                     'step #%d' % (plugin, step_number))
        app = get_app()
        if (app.protocol and not app.running and not app.realtime_mode and
            (plugin == 'microdrop.gui.dmf_device_controller' or plugin ==
             self.name) and app.protocol.current_step_number == step_number):
            self.on_step_run()

    def on_step_swapped(self, original_step_number, new_step_number):
        logger.debug('[DropBotPlugin] on_step_swapped():'
                     'original_step_number=%d, new_step_number=%d' %
                     (original_step_number, new_step_number))
        self.on_step_options_changed(self.name,
                                     get_app().protocol.current_step_number)

    def on_experiment_log_changed(self, log):
        # Check if the experiment log already has control board meta data, and
        # if so, return.
        data = log.get("control board name")
        for val in data:
            if val:
                return

        # add the name, hardware version, id, and firmware version to the experiment
        # log metadata
        data = {}
        if self.control_board:
            data["control board name"] = self.control_board.properties['display_name']
            data["control board id"] = \
                self.control_board.id
            data["control board uuid"] = \
                self.control_board.uuid
            data["control board hardware version"] = (self.control_board
                                                      .hardware_version)
            data["control board software version"] = (self.control_board
                                                      .properties['software_version'])
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

from ._version import get_versions
__version__ = get_versions()['version']
del get_versions
