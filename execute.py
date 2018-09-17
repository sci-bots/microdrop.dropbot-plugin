'''
.. versionadded:: 2.37
'''
import logging

from logging_helpers import _L
import dropbot as db
import dropbot.hardware_test
import dropbot.self_test
import dropbot.threshold
import numpy as np
import pandas as pd
import si_prefix as si
import trollius as asyncio


NAME = 'dropbot_plugin'


@asyncio.coroutine
def actuate(proxy, dmf_device, electrode_states, duration_s=0,
            volume_threshold=0, c_unit_area=None):
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

    c_unit_area : float, optional
        Specific capacitance, i.e., units of $F/mm^2$.

    Returns
    -------
    actuated_electrodes : list
        List of actuated electrode IDs.
    '''
    requested_electrodes = electrode_states[electrode_states > 0].index
    requested_channels = (dmf_device.channels_by_electrode
                          .loc[requested_electrodes])

    actuated_channels = pd.Series()
    actuated_area = 0

    channels_updated = asyncio.Event()

    def _on_channels_updated(message):
        '''
        Message keys:
            - ``"n"``: number of actuated channel
            - ``"actuated"``: list of actuated channel identifiers.
            - ``"start"``: ms counter before setting shift registers
            - ``"end"``: ms counter after setting shift registers
        '''
        global actuated_area
        global actuated_channels

        actuated_channels = message['actuated']

        if actuated_channels:
            actuated_electrodes = \
                dmf_device.actuated_electrodes(actuated_channels).dropna()
            actuated_areas = \
                dmf_device.electrode_areas.ix[actuated_electrodes.values]
            actuated_area = actuated_areas.sum()
        else:
            actuated_area = 0
        # m^2 area
        area = actuated_area * (1e-3 ** 2)
        # Approximate area in SI units.
        value, pow10 = si.split(np.sqrt(area))
        si_unit = si.SI_PREFIX_UNITS[len(si.SI_PREFIX_UNITS) // 2 +
                                        pow10 // 3]
        status = ('actuated electrodes: %s (%.1f %sm^2)' % (actuated_channels,
                                                            value ** 2,
                                                            si_unit))
        _L().debug(status)
        channels_updated.set()

    proxy.signals.signal('channels-updated').connect(_on_channels_updated)

    # Criteria that must be met to set target capacitance.
    threshold_criteria = [duration_s > 0,
                          volume_threshold > 0,
                          len(requested_electrodes) > 0,
                          c_unit_area is not None]
    _L().debug('threshold_criteria: `%s`', threshold_criteria)

    result = {}

    if not all(threshold_criteria):
        # ## Case 1: no volume threshold specified.
        #  1. Set control board state of channels according to requested
        #     actuation states.
        #  2. Wait for channels to be actuated.
        actuated_channels = \
            db.threshold.actuate_channels(proxy, requested_channels, timeout=5)

        #  3. Connect to `capacitance-updated` signal to record capacitance
        #     values measured during the step.
        capacitance_messages = []

        def _on_capacitance_updated(message):
            message['actuated_channels'] = actuated_channels
            message['actuated_area'] = actuated_area
            capacitance_messages.append(message)

        proxy.signals.signal('capacitance-updated')\
            .connect(_on_capacitance_updated)
        #  4. Delay for specified duration.
        try:
            yield asyncio.From(asyncio.sleep(duration_s))
        finally:
            proxy.signals.signal('capacitance-updated')\
                .disconnect(_on_capacitance_updated)
    else:
        # ## Case 2: volume threshold specified.
        #
        # A volume threshold has been set for this step.

        # Calculate target capacitance based on actuated area.
        #
        # Note: `app_values['c_liquid']` represents a *specific
        # capacitance*, i.e., has units of $F/mm^2$.
        actuated_areas = (dmf_device.electrode_areas
                          .ix[requested_electrodes.values])
        actuated_area = actuated_areas.sum()

        meters_squared_area = actuated_area * (1e-3 ** 2)  # m^2 area
        # Approximate length of unit side in SI units.
        si_length, pow10 = si.split(np.sqrt(meters_squared_area))
        si_unit = si.SI_PREFIX_UNITS[len(si.SI_PREFIX_UNITS) // 2 +
                                     pow10 // 3]

        target_capacitance = volume_threshold * actuated_area * c_unit_area

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
            db.threshold.co_target_capacitance(proxy,
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

            result['threshold'] = {'target': dropbot_event['target'],
                                   'measured': dropbot_event['new_value'],
                                   'start': dropbot_event['start'],
                                   'end': dropbot_event['end']}

            # Show notification in main window status bar.
            if logger.getEffectiveLevel() <= logging.DEBUG:
                status = ('reached %sF (> %sF) over electrodes: %s (%.1f '
                          '%sm^2) after %ss' %
                          (si.si_format(result['threshold']['measured']),
                           si.si_format(result['threshold']['target']),
                           actuated_channels, si_length ** 2, si_unit,
                           (dropbot_event['end'] -
                            dropbot_event['start']).total_seconds()))
                logger.debug(status)
        except asyncio.TimeoutError:
            raise RuntimeError('Timed out waiting for target capacitance.')

    yield asyncio.From(channels_updated.wait())
    actuated_electrodes = (dmf_device.electrodes_by_channel
                           .loc[actuated_channels])

    # Return list of actuated channels (which _may_ be fewer than the
    # number of requested actuated channels if one or more channels is
    # _disabled_).
    result.update({'actuated_electrodes': actuated_electrodes,
                   'capacitance_messages': capacitance_messages})

    raise asyncio.Return(result)


@asyncio.coroutine
def execute(proxy, dmf_device, plugin_kwargs, signals):
    '''
    Parameters
    ----------
    plugin_kwargs : dict
        Plugin settings as JSON serializable dictionary.
    signals : blinker.Namespace
        Signals namespace.
    '''
    def verify_connected(coro):
        @asyncio.coroutine
        def _wrapped(*args, **kwargs):
            if proxy is None:
                raise RuntimeError('DropBot not connected.')
            result = yield asyncio.From(coro(*args, **kwargs))
            raise asyncio.Return(result)
        return _wrapped

    @verify_connected
    @asyncio.coroutine
    def _set_frequency(frequency):
        proxy.frequency = frequency

    @verify_connected
    @asyncio.coroutine
    def _set_voltage(voltage):
        proxy.voltage = voltage

    @verify_connected
    @asyncio.coroutine
    def on_actuation_request(electrode_states, duration_s=0):
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
        '''
        try:
            result = yield asyncio\
                .From(actuate(proxy, dmf_device,
                              electrode_states, duration_s=duration_s,
                              volume_threshold=volume_threshold,
                              c_unit_area=c_unit_area))
            # Notify other plugins that actuation completed.
            responses = signals.signal('actuation-completed')\
                .send('dropbot_plugin', **result)
            yield asyncio.From(asyncio.gather(*(r[1] for r in responses)))
        except:
            logging.info('on_actuation_request', exc_info=True)
            raise
        else:
            raise asyncio.Return(result['actuated_electrodes'])

    kwargs = plugin_kwargs.get(NAME, {})
    volume_threshold = kwargs.get('volume_threshold')
    c_unit_area = kwargs.get('c_unit_area')

    signals.signal('set-frequency').connect(_set_frequency, weak=False)
    signals.signal('set-voltage').connect(_set_voltage, weak=False)
    signals.signal('on-actuation-request').connect(on_actuation_request,
                                                   weak=False)
