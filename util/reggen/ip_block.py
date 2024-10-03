# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
'''Code representing an IP block for reggen'''

import logging as log
from typing import Dict, List, Optional, Sequence, Set, Tuple

import hjson  # type: ignore
from reggen.alert import Alert
from reggen.bus_interfaces import BusInterfaces
from reggen.clocking import Clocking, ClockingItem
from reggen.countermeasure import CounterMeasure
from reggen.feature import Feature
from reggen.inter_signal import InterSignal
from reggen.interrupt import Interrupt
from reggen.lib import (check_bool, check_int, check_keys, check_list,
                        check_name)
from reggen.params import LocalParam, ReggenParams
from reggen.reg_block import RegBlock
from reggen.signal import Signal
from semantic_version import Version

# Known unique comportable IP names and associated CIP_IDs.
KNOWN_CIP_IDS = {
    1: 'adc_ctrl',
    2: 'aes',
    3: 'aon_timer',
    4: 'clkmgr',
    5: 'csrng',
    6: 'edn',
    7: 'entropy_src',
    8: 'flash_ctrl',
    9: 'gpio',
    10: 'hmac',
    11: 'i2c',
    12: 'keymgr',
    13: 'kmac',
    14: 'lc_ctrl',
    15: 'otbn',
    16: 'otp_ctrl',
    17: 'pattgen',
    18: 'pinmux',
    19: 'pwm',
    20: 'pwrmgr',
    21: 'rom_ctrl',
    22: 'rstmgr',
    23: 'rv_core_ibex',
    24: 'rv_dm',
    25: 'rv_timer',
    26: 'spi_device',
    27: 'spi_host',
    28: 'sram_ctrl',
    29: 'sysrst_ctrl',
    30: 'uart',
    31: 'usbdev',
    32: 'alert_handler',
    33: 'rv_plic',
    34: 'ast',
    35: 'sensor_ctrl',
    36: 'dma',
    37: 'mbx',
    38: 'soc_proxy',
    39: 'keymgr_dpe',
    40: 'ascon',
    41: 'ac_range_check',
    42: 'soc_dbg_ctrl',
    43: 'racl_ctrl',
    44: 'prim_otp',
}

REQUIRED_ALIAS_FIELDS = {
    'alias_impl': ['s', "identifier for this alias implementation"],
    'alias_target': ['s', "name of the component to apply the alias file to"],
    'registers': ['l', "list of alias register definition groups"],
    'bus_interfaces': ['l', "bus interfaces for the device"],
}

# TODO: we may want to support for countermeasure and parameter aliases
# in the future.
OPTIONAL_ALIAS_FIELDS: Dict[str, List[str]] = {}

REQUIRED_FIELDS = {
    'name': ['s', "name of the component"],
    'cip_id': ['d', "unique comportable IP identifier"],
    'clocking': ['l', "clocking for the device"],
    'bus_interfaces': ['l', "bus interfaces for the device"],
    'registers':
    ['l', "list of register definition groups and "
     "offset control groups"]
}

OPTIONAL_FIELDS = {
    'human_name': ['s', "human-readable name of the component"],
    'one_line_desc': ['s', "one-line description of the component"],
    'one_paragraph_desc': ['s', "one-paragraph description of the component"],
    # Note: this revision list may be deprecated in the future.
    'revisions': ['l', "list with revision records"],
    'design_spec':
    ['s', "path to the design specification, relative to repo root"],
    'dv_doc': ['s', "path to the DV document, relative to repo root"],
    'hw_checklist': ['s', "path to the hw_checklist, relative to repo root"],
    'sw_checklist': ['s', "path to the sw_checklist, relative to repo root"],
    'design_stage': ['s', "design stage of module"],
    'dif_stage': ['s', 'DIF stage of module'],
    'verification_stage': ['s', "verification stage of module"],
    'notes': ['s', "random notes"],
    'version': ['s', "module version"],
    'life_stage': ['s', "life stage of module"],
    'commit_id': ['s', "commit ID of last stage sign-off"],
    'alert_list': ['lnw', "list of peripheral alerts"],
    'available_inout_list': ['lnw', "list of available peripheral inouts"],
    'available_input_list': ['lnw', "list of available peripheral inputs"],
    'available_output_list': ['lnw', "list of available peripheral outputs"],
    'expose_reg_if': ['pb', 'if set, expose reg interface in reg2hw signal'],
    'interrupt_list': ['lnw', "list of peripheral interrupts"],
    'inter_signal_list': ['l', "list of inter-module signals"],
    'no_auto_alert_regs': [
        's', "Set to true to suppress automatic "
        "generation of alert test registers. "
        "Defaults to true if no alert_list is present. "
        "Otherwise this defaults to false."
    ],
    'no_auto_intr_regs': [
        's', "Set to true to suppress automatic "
        "generation of interrupt registers. "
        "Defaults to true if no interrupt_list is present. "
        "Otherwise this defaults to false."
    ],
    'param_list': ['lp', "list of parameters of the IP"],
    'regwidth': ['d', "width of registers in bits (default 32)"],
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
    'wakeup_list': ['lnw', "list of peripheral wakeups"],
    'countermeasures': ["ln", "list of countermeasures in this block"],
    'features': ["ln", "list of functional features in this block"],
}

# Note that the revisions list may be deprecated in the future.
REQUIRED_REVISIONS_FIELDS = {
    'design_stage': ['s', "design stage of module"],
    'verification_stage': ['s', "verification stage of module"],
    'version': ['s', "semantic module version in the format x.y.z[+res#]"],
    'life_stage': ['s', "life stage of module"],
}

OPTIONAL_REVISIONS_FIELDS = {
    'dif_stage': ['s', 'DIF stage of module'],
    'commit_id': ['s', "commit ID of last stage sign-off"],
    'notes': ['s', "random notes"],
}


class IpBlock:

    def __init__(self,
                 name: str,
                 cip_id: int,
                 version: Version,
                 regwidth: int,
                 params: ReggenParams,
                 reg_blocks: Dict[Optional[str], RegBlock],
                 alias_impl: Optional[str],
                 interrupts: Sequence[Interrupt],
                 no_auto_intr: bool,
                 alerts: List[Alert],
                 no_auto_alert: bool,
                 scan: bool,
                 inter_signals: List[InterSignal],
                 bus_interfaces: BusInterfaces,
                 clocking: Clocking,
                 xputs: Tuple[Sequence[Signal], Sequence[Signal],
                              Sequence[Signal]],
                 wakeups: Sequence[Signal],
                 reset_requests: Sequence[Signal],
                 expose_reg_if: bool,
                 scan_reset: bool,
                 scan_en: bool,
                 countermeasures: List[CounterMeasure],
                 features: List[Feature],
                 node: str = ''):
        assert reg_blocks

        # Filter the interfaces and reg_blocks if request to build only for a
        # specific reg_block node.
        dev_if_names = []  # type: List[Optional[str]]
        if node:
            dev_if_names += [
                i for i in bus_interfaces.named_devices if i == node
            ]
            reg_blocks = {k: v for k, v in reg_blocks.items() if k == node}
        else:
            dev_if_names += bus_interfaces.named_devices

        # Check that register blocks are in bijection with device interfaces
        reg_block_names = reg_blocks.keys()
        if bus_interfaces.has_unnamed_device:
            dev_if_names.append(None)
        assert set(reg_block_names) == set(dev_if_names)

        self.name = name
        self.cip_id = cip_id
        self.version = version
        self.regwidth = regwidth
        self.reg_blocks = reg_blocks
        self.alias_impl = alias_impl
        self.params = params
        self.interrupts = interrupts
        self.no_auto_intr = no_auto_intr
        self.alerts = alerts
        self.no_auto_alert = no_auto_alert
        self.scan = scan
        self.inter_signals = inter_signals
        self.bus_interfaces = bus_interfaces
        self.clocking = clocking
        self.xputs = xputs
        self.wakeups = wakeups
        self.reset_requests = reset_requests
        self.expose_reg_if = expose_reg_if
        self.scan_reset = scan_reset
        self.scan_en = scan_en
        self.countermeasures = countermeasures
        self.features = features

    @staticmethod
    def from_raw(param_defaults: List[Tuple[str, str]],
                 raw: object,
                 where: str,
                 node: str = '') -> 'IpBlock':

        rd = check_keys(raw, 'block at ' + where, list(REQUIRED_FIELDS.keys()),
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
                                 '{} is not positive.'.format(what, regwidth))

        params = ReggenParams.from_raw('parameter list for ' + what,
                                       rd.get('param_list', []))
        try:
            params.apply_defaults(param_defaults)
        except (ValueError, KeyError) as err:
            raise ValueError(
                'Failed to apply defaults to params: {}'.format(err)) from None

        init_block = RegBlock(regwidth, params)

        interrupts = Interrupt.from_raw_list(
            'interrupt_list for block {}'.format(name),
            rd.get('interrupt_list', []))
        alerts = Alert.from_raw_list('alert_list for block {}'.format(name),
                                     rd.get('alert_list', []))
        known_cms = {}
        raw_cms = rd.get('countermeasures', [])

        countermeasures = CounterMeasure.from_raw_list(
            'countermeasure list for block {}'.format(name), raw_cms)

        features = Feature.from_raw_list(
            'feature list for block {}'.format(name), rd.get('features', []))

        # Ensure that the countermeasures are unique
        for x in countermeasures:
            if str(x) in known_cms:
                raise RuntimeError(f"Duplicate countermeasure {str(x)}")
            else:
                known_cms.update({str(x): 1})

        cip_id = check_int(rd.get('cip_id'), 'cip id for ' + what)
        # In case there are multiple past revisions of this IP, always pick the
        # newest one. Note: this revision list may be deprecated in the
        # future.
        version = Version('0.0.0')
        if 'revisions' in rd:
            for rev in check_list(rd['revisions'], what):
                rev = check_keys(rev, 'rev item at ' + what,
                                 list(REQUIRED_REVISIONS_FIELDS.keys()),
                                 list(OPTIONAL_REVISIONS_FIELDS.keys()))
                try:
                    ver = Version(rev['version'])
                except ValueError as err:
                    raise RuntimeError(str(err) + ' in ' + what)
                version = ver if ver >= version else version
        else:
            try:
                version = Version(rd.get('version'))
            except ValueError as err:
                raise RuntimeError(str(err) + ' in ' + what)

        no_auto_intr = check_bool(rd.get('no_auto_intr_regs', not interrupts),
                                  'no_auto_intr_regs field of ' + what)

        no_auto_alert = check_bool(rd.get('no_auto_alert_regs', not alerts),
                                   'no_auto_alert_regs field of ' + what)

        if interrupts and not no_auto_intr:
            if interrupts[-1].bits.msb >= regwidth:
                raise ValueError("Too many interrupts defined for {}: "
                                 "msb is {}, which doesn't fit with a "
                                 "regwidth of {}.".format(
                                     what, interrupts[-1].bits.msb, regwidth))
            init_block.make_intr_regs(interrupts)

        if alerts:
            if not no_auto_alert:
                if len(alerts) > regwidth:
                    raise ValueError(
                        "Too many alerts defined for {}: "
                        "{} alerts don't fit with a regwidth of {}.".format(
                            what, len(alerts), regwidth))
                init_block.make_alert_regs(alerts)

        # Generate a NumAlerts parameter
        if alerts:
            existing_param = params.get('NumAlerts')
            if existing_param is not None:
                if ((not isinstance(existing_param, LocalParam) or
                     existing_param.param_type != 'int' or
                     existing_param.value != str(len(alerts)))):
                    raise ValueError('Conflicting definition of NumAlerts '
                                     f'parameter in {what}.')
            else:
                params.add(
                    LocalParam(name='NumAlerts',
                               desc='Number of alerts',
                               param_type='int',
                               value=str(len(alerts)),
                               unpacked_dimensions=None))

        scan = check_bool(rd.get('scan', False), 'scan field of ' + what)

        r_inter_signals = check_list(rd.get('inter_signal_list', []),
                                     'inter_signal_list field')
        inter_signals = [
            InterSignal.from_raw(
                params,
                f'entry {idx + 1} of the inter_signal_list field in {what}',
                entry) for idx, entry in enumerate(r_inter_signals)
        ]

        bus_interfaces = (BusInterfaces.from_raw(
            rd['bus_interfaces'], 'bus_interfaces field of ' + where))
        inter_signals += bus_interfaces.inter_signals()

        clocking = Clocking.from_raw(rd['clocking'],
                                     'clocking field of ' + what)

        reg_blocks = RegBlock.build_blocks(init_block, rd['registers'],
                                           bus_interfaces, clocking, False)

        xputs = (Signal.from_raw_list('available_inout_list for block ' + name,
                                      rd.get('available_inout_list', [])),
                 Signal.from_raw_list('available_input_list for block ' + name,
                                      rd.get('available_input_list', [])),
                 Signal.from_raw_list(
                     'available_output_list for block ' + name,
                     rd.get('available_output_list', [])))
        wakeups = Signal.from_raw_list('wakeup_list for block ' + name,
                                       rd.get('wakeup_list', []))
        rst_reqs = Signal.from_raw_list('reset_request_list for block ' + name,
                                        rd.get('reset_request_list', []))

        expose_reg_if = check_bool(rd.get('expose_reg_if', False),
                                   'expose_reg_if field of ' + what)

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
                             "by {}).".format(name, dev_if_names,
                                              list(reg_block_names)))

        return IpBlock(name, cip_id, version, regwidth, params, reg_blocks,
                       None, interrupts, no_auto_intr, alerts, no_auto_alert,
                       scan, inter_signals, bus_interfaces, clocking, xputs,
                       wakeups, rst_reqs, expose_reg_if, scan_reset, scan_en,
                       countermeasures, features, node)

    @staticmethod
    def from_text(txt: str,
                  param_defaults: List[Tuple[str, str]],
                  where: str,
                  node: str = '') -> 'IpBlock':
        '''Load an IpBlock from an hjson description in txt'''
        return IpBlock.from_raw(param_defaults,
                                hjson.loads(txt, use_decimal=True), where,
                                node)

    @staticmethod
    def from_path(path: str, param_defaults: List[Tuple[str,
                                                        str]]) -> 'IpBlock':
        '''Load an IpBlock from an hjson description in a file at path'''
        with open(path, 'r', encoding='utf-8') as handle:
            return IpBlock.from_text(handle.read(), param_defaults,
                                     'file at {!r}'.format(path))

    def alias_from_raw(self, scrub: bool, raw: object, where: str) -> None:
        '''Parses and validates an alias reg block and adds it to this IpBlock.

        The alias register definitions are compared with the corresponding
        generic register definitions in self.reg_blocks to ensure that the
        register and field structure is the same. Only a subset of register
        and field attributes may differ and all other attributes must be
        identical. The overridable attributes are defined in register.py and
        field.py, but typically comprise attributes like 'name', 'desc',
        'resval' and 'tags'.

        The alias register information is then applied to the self.reg_blocks
        datastructure. Generic register descriptions with no associated alias
        register definition just remain unmodified, meaning that the user can
        choose to only provide alias overrides for a subset of all registers.
        The resulting "augmented" register block is therefore always guaranteed
        to be structurally identical to the unmodified generic register block.

        Note that the alias register definition also overrides the hier_path
        variable associated with the corresponding bus interfaces.

        Setting the scrub argument to True will scrub sensitive fields in the
        alias definition and replace the entire register block of the target
        interface with the scrubbed alias reg block. This is helpful to create
        the generic CSR structure matching the alias definition automatically.
        '''
        rd = check_keys(raw, 'block at ' + where,
                        list(REQUIRED_ALIAS_FIELDS.keys()),
                        list(OPTIONAL_ALIAS_FIELDS.keys()))

        alias_bus_interfaces = (BusInterfaces.from_raw(
            rd['bus_interfaces'], 'bus_interfaces of block at ' + where))
        if ((alias_bus_interfaces.has_unnamed_host or
             alias_bus_interfaces.named_hosts)):
            raise ValueError("Alias registers cannot be defined for host "
                             "interfaces (in block at {}).".format(where))
        # Alias register definitions are only compatible with named devices.
        if ((alias_bus_interfaces.has_unnamed_device or
             self.bus_interfaces.has_unnamed_device)):
            raise ValueError("Alias registers must use named devices "
                             "(in block at {}).".format(where))

        # Check that the device interface names are
        # a subset of the already defined register blocks
        bus_device_names = set(self.bus_interfaces.named_devices)
        alias_bus_device_names = set(alias_bus_interfaces.named_devices)
        if not alias_bus_device_names.issubset(bus_device_names):
            raise ValueError("Alias file {} refers to device names {} that "
                             "do not map to device names in {}.".format(
                                 where, list(alias_bus_device_names),
                                 self.name))

        self.alias_impl = check_name(rd['alias_impl'],
                                     'alias_impl of block at ' + where)

        alias_target = check_name(rd['alias_target'],
                                  'alias_target of block at ' + where)

        if alias_target != self.name:
            raise ValueError("Alias target block name {} in {} "
                             "does not match block name {}.".format(
                                 alias_target, where, self.name))

        init_block = RegBlock(self.regwidth, self.params)

        alias_reg_blocks = RegBlock.build_blocks(init_block, rd['registers'],
                                                 self.bus_interfaces,
                                                 self.clocking, True)

        # Check that alias register block names are
        # a subset of the already defined register blocks
        alias_reg_block_names = set(alias_reg_blocks.keys())

        if not alias_reg_block_names.issubset(set(self.reg_blocks.keys())):
            raise ValueError("Alias file {} refers to register blocks {} that "
                             "do not map to register blocks in {}.".format(
                                 where, list(alias_reg_block_names),
                                 self.name))

        # Check that the alias bus interface names and register blocks match
        if alias_reg_block_names != alias_bus_device_names:
            raise ValueError("Interface and register block names do not match "
                             "in {}.".format(where))

        # Validate alias registers against the generic reg blocks,
        # and enhance the information in the existing datastructures.
        for block_key, alias_block in alias_reg_blocks.items():
            # Double check the interface definition options
            if self.bus_interfaces.device_async:
                if not alias_bus_interfaces.device_async:
                    raise ValueError('Missing device_async key in alias '
                                     'interface {} in {}'.format(
                                         block_key, where))
                if ((alias_bus_interfaces.device_async[block_key] !=
                     self.bus_interfaces.device_async[block_key])):
                    raise ValueError('Inconsistent configuration of interface '
                                     '{} in {}'.format(block_key, where))

            if scrub:
                # scrub alias definitions and replace the entire block.
                alias_block.scrub_alias(where)
                self.reg_blocks[block_key] = alias_block
            else:
                # Override hier path of aliased interface
                hier_path = alias_bus_interfaces.device_hier_paths[block_key]
                self.bus_interfaces.device_hier_paths[block_key] = hier_path

                # Validate and apply alias definitions
                self.reg_blocks[block_key].apply_alias(alias_block, where)

    def alias_from_text(self, scrub: bool, txt: str, where: str) -> None:
        '''Load alias regblocks from an hjson description in txt'''
        self.alias_from_raw(scrub, hjson.loads(txt, use_decimal=True), where)

    def alias_from_path(self, scrub: bool, path: str) -> None:
        '''Load alias regblocks from an hjson description in a file at path'''
        with open(path, 'r', encoding='utf-8') as handle:
            self.alias_from_text(scrub, handle.read(),
                                 'alias file at {!r}'.format(path))

    def _asdict(self) -> Dict[str, object]:
        ret = {'name': self.name, 'regwidth': self.regwidth}
        if len(self.reg_blocks) == 1 and None in self.reg_blocks:
            ret['registers'] = self.reg_blocks[None].as_dicts()
        else:
            ret['registers'] = {
                k: v.as_dicts()
                for k, v in self.reg_blocks.items()
            }

        ret['param_list'] = self.params.as_dicts()
        ret['cip_id'] = self.cip_id
        ret['version'] = str(self.version)
        ret['interrupt_list'] = self.interrupts
        ret['no_auto_intr_regs'] = self.no_auto_intr
        ret['alert_list'] = self.alerts
        ret['no_auto_alert_regs'] = self.no_auto_alert
        ret['scan'] = self.scan
        ret['inter_signal_list'] = self.inter_signals
        ret['bus_interfaces'] = self.bus_interfaces.as_dicts()

        ret['clocking'] = self.clocking.items

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

    def get_signals_as_list_of_dicts(self) -> List[Dict[str, object]]:
        '''Look up and return signal by name'''
        result = []
        for iodir, xput in zip(('inout', 'input', 'output'), self.xputs):
            for sig in xput:
                result.append(sig.as_nwt_dict(iodir))
        return result

    def get_signal_by_name_as_dict(self, name: str) -> Dict[str, object]:
        '''Look up and return signal by name'''
        sig_list = self.get_signals_as_list_of_dicts()
        for sig in sig_list:
            if sig['name'] == name:
                return sig
        else:
            raise ValueError("Signal {} does not exist in IP block {}".format(
                name, self.name))

    def has_shadowed_reg(self) -> bool:
        '''Return boolean indication whether reg block contains shadowed registers'''

        for rb in self.reg_blocks.values():
            if rb.has_shadowed_reg():
                return True

        # if we are here, then no one has a shadowed register
        return False

    def get_primary_clock(self) -> ClockingItem:
        '''Return primary clock of an block'''

        return self.clocking.primary

    def check_cm_annotations(self, rtl_names: Dict[str, List[Tuple[str, int]]],
                             hjson_path: str) -> bool:
        '''Check RTL annotations against countermeasure list of this block'''

        return CounterMeasure.check_annotation_list(self.name, hjson_path,
                                                    rtl_names,
                                                    self.countermeasures)

    def check_regwens(self) -> bool:
        """Checks all regwens are used in at least one other CSR

        This relies on the regwen having the string "REGWEN" in its name.
        The uses should be in the "regwen" field of a CSR.
        """
        log.debug(f"Checking regwens for IP {self.name}")
        status: bool = True
        for rb in self.reg_blocks.values():
            rb_name = rb.name if rb.name else "default"
            log.debug(f"Register block: {rb_name}")
            regwen_names: List[str] = [
                reg.name for reg in rb.registers if "REGWEN" in reg.name
            ]
            unused_regwens: List[str] = []
            for regwen in regwen_names:
                regwen_users = []
                for reg in rb.registers:
                    if reg.regwen == regwen:
                        regwen_users.append(reg)
                for multi_reg in rb.multiregs:
                    for reg in multi_reg.pregs:
                        if reg.regwen == regwen:
                            regwen_users.append(reg)
                if not regwen_users:
                    unused_regwens.append(regwen)
                else:
                    log.debug(
                        f"Regwen {regwen} in {self.name}'s {rb_name} register "
                        "block controls the following registers:")
                    for r in regwen_users:
                        log.debug(f"  {r.name}")
            if unused_regwens:
                log.error(f"Unused regwen(s) in {self.name} {rb_name} "
                          f"register block: {', '.join(unused_regwens)}")
                status = False
        return status
