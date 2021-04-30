# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code representing an IP block for reggen'''

from typing import Dict, List, Optional, Sequence, Set, Tuple

import hjson  # type: ignore

from .alert import Alert
from .bus_interfaces import BusInterfaces
from .inter_signal import InterSignal
from .lib import (check_keys, check_name, check_int, check_bool,
                  check_list, check_optional_str, check_name_list)
from .params import ReggenParams, LocalParam
from .reg_block import RegBlock
from .signal import Signal


REQUIRED_FIELDS = {
    'name': ['s', "name of the component"],
    'clock_primary': ['s', "name of the primary clock"],
    'bus_interfaces': ['l', "bus interfaces for the device"],
    'registers': [
        'l',
        "list of register definition groups and "
        "offset control groups"
    ]
}

OPTIONAL_FIELDS = {
    'alert_list': ['lnw', "list of peripheral alerts"],
    'available_inout_list': ['lnw', "list of available peripheral inouts"],
    'available_input_list': ['lnw', "list of available peripheral inputs"],
    'available_output_list': ['lnw', "list of available peripheral outputs"],
    'hier_path': [
        None,
        'additional hierarchy path before the reg block instance'
    ],
    'interrupt_list': ['lnw', "list of peripheral interrupts"],
    'inter_signal_list': ['l', "list of inter-module signals"],
    'no_auto_alert_regs': [
        's', "Set to true to suppress automatic "
        "generation of alert test registers. "
        "Defaults to true if no alert_list is present. "
        "Otherwise this defaults to false. "
    ],
    'no_auto_intr_regs': [
        's', "Set to true to suppress automatic "
        "generation of interrupt registers. "
        "Defaults to true if no interrupt_list is present. "
        "Otherwise this defaults to false. "
    ],
    'other_clock_list': ['l', "list of other chip clocks needed"],
    'other_reset_list': ['l', "list of other resets"],
    'param_list': ['lp', "list of parameters of the IP"],
    'regwidth': ['d', "width of registers in bits (default 32)"],
    'reset_primary': ['s', "primary reset used by the module"],
    'reset_request_list': ['l', 'list of signals requesting reset'],
    'scan': ['pb', 'Indicates the module have `scanmode_i`'],
    'scan_reset': ['pb', 'Indicates the module have `scan_rst_ni`'],
    'scan_en': ['pb', 'Indicates the module has `scan_en_i`'],
    'SPDX-License-Identifier': [
        's', "License ientifier (if using pure json) "
        "Only use this if unable to put this "
        "information in a comment at the top of the "
        "file."
    ],
    'wakeup_list': ['lnw', "list of peripheral wakeups"]
}


class IpBlock:
    def __init__(self,
                 name: str,
                 regwidth: int,
                 params: ReggenParams,
                 reg_blocks: Dict[Optional[str], RegBlock],
                 interrupts: Sequence[Signal],
                 no_auto_intr: bool,
                 alerts: List[Alert],
                 no_auto_alert: bool,
                 scan: bool,
                 inter_signals: List[InterSignal],
                 bus_interfaces: BusInterfaces,
                 hier_path: Optional[str],
                 clock_signals: List[str],
                 reset_signals: List[str],
                 xputs: Tuple[Sequence[Signal],
                              Sequence[Signal],
                              Sequence[Signal]],
                 wakeups: Sequence[Signal],
                 reset_requests: Sequence[Signal],
                 scan_reset: bool,
                 scan_en: bool):
        assert reg_blocks
        assert clock_signals
        assert reset_signals

        # Check that register blocks are in bijection with device interfaces
        reg_block_names = reg_blocks.keys()
        dev_if_names = []  # type: List[Optional[str]]
        dev_if_names += bus_interfaces.named_devices
        if bus_interfaces.has_unnamed_device:
            dev_if_names.append(None)
        assert set(reg_block_names) == set(dev_if_names)

        self.name = name
        self.regwidth = regwidth
        self.reg_blocks = reg_blocks
        self.params = params
        self.interrupts = interrupts
        self.no_auto_intr = no_auto_intr
        self.alerts = alerts
        self.no_auto_alert = no_auto_alert
        self.scan = scan
        self.inter_signals = inter_signals
        self.bus_interfaces = bus_interfaces
        self.hier_path = hier_path
        self.clock_signals = clock_signals
        self.reset_signals = reset_signals
        self.xputs = xputs
        self.wakeups = wakeups
        self.reset_requests = reset_requests
        self.scan_reset = scan_reset
        self.scan_en = scan_en

    @staticmethod
    def from_raw(param_defaults: List[Tuple[str, str]],
                 raw: object,
                 where: str) -> 'IpBlock':

        rd = check_keys(raw, 'block at ' + where,
                        list(REQUIRED_FIELDS.keys()),
                        list(OPTIONAL_FIELDS.keys()))

        name = check_name(rd['name'], 'name of block at ' + where)

        what = '{} block at {}'.format(name, where)

        r_regwidth = rd.get('regwidth')
        if r_regwidth is None:
            regwidth = 32
        else:
            regwidth = check_int(r_regwidth, 'regwidth field of ' + what)
            if regwidth <= 0:
                raise ValueError('Invalid regwidth field for {}: '
                                 '{} is not positive.'
                                 .format(what, regwidth))

        params = ReggenParams.from_raw('parameter list for ' + what,
                                       rd.get('param_list', []))
        try:
            params.apply_defaults(param_defaults)
        except (ValueError, KeyError) as err:
            raise ValueError('Failed to apply defaults to params: {}'
                             .format(err)) from None

        init_block = RegBlock(regwidth, params)

        interrupts = Signal.from_raw_list('interrupt_list for block {}'
                                          .format(name),
                                          rd.get('interrupt_list', []))
        alerts = Alert.from_raw_list('alert_list for block {}'
                                     .format(name),
                                     rd.get('alert_list', []))

        no_auto_intr = check_bool(rd.get('no_auto_intr_regs', not interrupts),
                                  'no_auto_intr_regs field of ' + what)

        no_auto_alert = check_bool(rd.get('no_auto_alert_regs', not alerts),
                                   'no_auto_alert_regs field of ' + what)

        if interrupts and not no_auto_intr:
            if interrupts[-1].bits.msb >= regwidth:
                raise ValueError("Interrupt list for {} is too wide: "
                                 "msb is {}, which doesn't fit with a "
                                 "regwidth of {}."
                                 .format(what,
                                         interrupts[-1].bits.msb, regwidth))
            init_block.make_intr_regs(interrupts)

        if alerts:
            if not no_auto_alert:
                if len(alerts) > regwidth:
                    raise ValueError("Interrupt list for {} is too wide: "
                                     "{} alerts don't fit with a regwidth of {}."
                                     .format(what, len(alerts), regwidth))
                init_block.make_alert_regs(alerts)

            # Generate a NumAlerts parameter
            existing_param = params.get('NumAlerts')
            if existing_param is not None:
                if ((not isinstance(existing_param, LocalParam) or
                     existing_param.param_type != 'int' or
                     existing_param.value != str(len(alerts)))):
                    raise ValueError('Conflicting definition of NumAlerts '
                                     'parameter.')
            else:
                params.add(LocalParam(name='NumAlerts',
                                      desc='Number of alerts',
                                      param_type='int',
                                      value=str(len(alerts))))

        scan = check_bool(rd.get('scan', False), 'scan field of ' + what)

        reg_blocks = RegBlock.build_blocks(init_block, rd['registers'])

        r_inter_signals = check_list(rd.get('inter_signal_list', []),
                                     'inter_signal_list field')
        inter_signals = [
            InterSignal.from_raw('entry {} of the inter_signal_list field'
                                 .format(idx + 1),
                                 entry)
            for idx, entry in enumerate(r_inter_signals)
        ]

        bus_interfaces = (BusInterfaces.
                          from_raw(rd['bus_interfaces'],
                                   'bus_interfaces field of ' + where))
        inter_signals += bus_interfaces.inter_signals()

        hier_path = check_optional_str(rd.get('hier_path', None),
                                       'hier_path field of ' + what)

        clock_primary = check_name(rd['clock_primary'],
                                   'clock_primary field of ' + what)
        other_clock_list = check_name_list(rd.get('other_clock_list', []),
                                           'other_clock_list field of ' + what)
        clock_signals = [clock_primary] + other_clock_list

        reset_primary = check_name(rd.get('reset_primary', 'rst_ni'),
                                   'reset_primary field of ' + what)
        other_reset_list = check_name_list(rd.get('other_reset_list', []),
                                           'other_reset_list field of ' + what)
        reset_signals = [reset_primary] + other_reset_list

        xputs = (
            Signal.from_raw_list('available_inout_list for block ' + name,
                                 rd.get('available_inout_list', [])),
            Signal.from_raw_list('available_input_list for block ' + name,
                                 rd.get('available_input_list', [])),
            Signal.from_raw_list('available_output_list for block ' + name,
                                 rd.get('available_output_list', []))
        )
        wakeups = Signal.from_raw_list('wakeup_list for block ' + name,
                                       rd.get('wakeup_list', []))
        rst_reqs = Signal.from_raw_list('reset_request_list for block ' + name,
                                        rd.get('reset_request_list', []))

        scan_reset = check_bool(rd.get('scan_reset', False),
                                'scan_reset field of ' + what)

        scan_en = check_bool(rd.get('scan_en', False),
                                'scan_en field of ' + what)

        # Check that register blocks are in bijection with device interfaces
        reg_block_names = reg_blocks.keys()
        dev_if_names = []  # type: List[Optional[str]]
        dev_if_names += bus_interfaces.named_devices
        if bus_interfaces.has_unnamed_device:
            dev_if_names.append(None)
        if set(reg_block_names) != set(dev_if_names):
            raise ValueError("IP block {} defines device interfaces, named {} "
                             "but its registers don't match (they are keyed "
                             "by {})."
                             .format(name, dev_if_names,
                                     list(reg_block_names)))

        return IpBlock(name, regwidth, params, reg_blocks,
                       interrupts, no_auto_intr, alerts, no_auto_alert,
                       scan, inter_signals, bus_interfaces,
                       hier_path, clock_signals, reset_signals, xputs,
                       wakeups, rst_reqs, scan_reset, scan_en)

    @staticmethod
    def from_text(txt: str,
                  param_defaults: List[Tuple[str, str]],
                  where: str) -> 'IpBlock':
        '''Load an IpBlock from an hjson description in txt'''
        return IpBlock.from_raw(param_defaults,
                                hjson.loads(txt, use_decimal=True),
                                where)

    @staticmethod
    def from_path(path: str,
                  param_defaults: List[Tuple[str, str]]) -> 'IpBlock':
        '''Load an IpBlock from an hjson description in a file at path'''
        with open(path, 'r', encoding='utf-8') as handle:
            return IpBlock.from_text(handle.read(), param_defaults,
                                     'file at {!r}'.format(path))

    def _asdict(self) -> Dict[str, object]:
        ret = {
            'name': self.name,
            'regwidth': self.regwidth
        }
        if len(self.reg_blocks) == 1 and None in self.reg_blocks:
            ret['registers'] = self.reg_blocks[None].as_dicts()
        else:
            ret['registers'] = {k: v.as_dicts()
                                for k, v in self.reg_blocks.items()}

        ret['param_list'] = self.params.as_dicts()
        ret['interrupt_list'] = self.interrupts
        ret['no_auto_intr_regs'] = self.no_auto_intr
        ret['alert_list'] = self.alerts
        ret['no_auto_alert_regs'] = self.no_auto_alert
        ret['scan'] = self.scan
        ret['inter_signal_list'] = self.inter_signals
        ret['bus_interfaces'] = self.bus_interfaces.as_dicts()

        if self.hier_path is not None:
            ret['hier_path'] = self.hier_path

        ret['clock_primary'] = self.clock_signals[0]
        if len(self.clock_signals) > 1:
            ret['other_clock_list'] = self.clock_signals[1:]

        ret['reset_primary'] = self.reset_signals[0]
        if len(self.reset_signals) > 1:
            ret['other_reset_list'] = self.reset_signals[1:]

        inouts, inputs, outputs = self.xputs
        if inouts:
            ret['available_inout_list'] = inouts
        if inputs:
            ret['available_input_list'] = inputs
        if outputs:
            ret['available_output_list'] = outputs

        if self.wakeups:
            ret['wakeup_list'] = self.wakeups
        if self.reset_requests:
            ret['reset_request_list'] = self.reset_requests

        ret['scan_reset'] = self.scan_reset
        ret['scan_en'] = self.scan_en

        return ret

    def get_rnames(self) -> Set[str]:
        ret = set()  # type: Set[str]
        for rb in self.reg_blocks.values():
            ret = ret.union(set(rb.name_to_offset.keys()))
        return ret

    def get_signals_as_list_of_dicts(self) -> List[Dict]:
        '''Look up and return signal by name'''
        result = []
        for iodir, xput in zip(('inout', 'input', 'output'), self.xputs):
            for sig in xput:
                result.append(sig.as_nwt_dict(iodir))
        return result

    def get_signal_by_name_as_dict(self, name: str) -> Dict:
        '''Look up and return signal by name'''
        sig_list = self.get_signals_as_list_of_dicts()
        for sig in sig_list:
            if sig['name'] == name:
                return sig
        else:
            raise ValueError("Signal {} does not exist in IP block {}"
                             .format(name, self.name))
