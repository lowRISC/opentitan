# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import re
from enum import Enum
from typing import Dict, List, Union

from basegen.typing import ConfigT
from reggen.ip_block import IpBlock
from reggen.validate import check_keys
from topgen.resets import Resets, UnmanagedResets
from topgen.typing import IpBlocksT

# For the reference
# val_types = {
#     'd': ["int", "integer (binary 0b, octal 0o, decimal, hex 0x)"],
#     'x': ["xint", "x for undefined otherwise int"],
#     'b': [
#         "bitrange", "bit number as decimal integer, \
#                     or bit-range as decimal integers msb:lsb"
#     ],
#     'l': ["list", "comma separated list enclosed in `[]`"],
#     'ln': ["name list", 'comma separated list enclosed in `[]` of '\
#            'one or more groups that have just name and dscr keys.'\
#            ' e.g. `{ name: "name", desc: "description"}`'],
#     'lnw': ["name list+", 'name list that optionally contains a width'],
#     'lp': ["parameter list", 'parameter list having default value optionally'],
#     'g': ["group", "comma separated group of key:value enclosed in `{}`"],
#     's': ["string", "string, typically short"],
#     't': ["text", "string, may be multi-line enclosed in `'''` "\
#           "may use `**bold**`, `*italic*` or `!!Reg` markup"],
#     'T': ["tuple", "tuple enclosed in ()"],
#     'pi': ["python int", "Native Python type int (generated)"],
#     'pb': ["python Bool", "Native Python type Bool (generated)"],
#     'pl': ["python list", "Native Python type list (generated)"],
#     'pe': ["python enum", "Native Python type enum (generated)"]
# }

# Required/optional field in top hjson
top_required = {
    'name': ['s', 'Top name'],
    'type': ['s', 'type of hjson. Shall be "top" always'],
    'clocks': ['g', 'group of clock properties'],
    'resets': ['l', 'list of resets'],
    'addr_spaces': ['g', 'list of address spaces'],
    'module': ['l', 'list of modules to instantiate'],
    'memory': [
        'l',
        'list of memories. At least one memory is needed to run the software'
    ],
    'xbar': ['l', 'List of the xbar used in the top'],
    'pinout': ['g', 'Pinout configuration'],
    'targets': ['l', ' Target configurations'],
    'pinmux': ['g', 'pinmux configuration'],
    'unmanaged_clocks': ['l', 'List of unmanaged external clocks']
}

top_optional = {
    'alert_module':
    ['l', 'list of the modules that connects to alert_handler'],
    'datawidth': ['pn', "default data width"],
    'exported_clks': ['g', 'clock signal routing rules'],
    'host': ['g', 'list of host-only components in the system'],
    'inter_module': ['g', 'define the signal connections between the modules'],
    'interrupt_module': ['l', 'list of the modules that connects to rv_plic'],
    'num_cores': ['pn', "number of computing units"],
    'outgoing_alert': ['g', 'the outgoing alert groups'],
    'outgoing_interrupt': ['g', 'the outgoing interrupt groups'],
    'power': ['g', 'power domains supported by the design'],
    'port': ['g', 'assign special attributes to specific ports'],
    'racl_config': ['s', 'Path to a RACL configuration HJSON file'],
    'reset_requests': ['g', 'define reset requests grouped by type'],
    'rnd_cnst_seed': ['int', "Seed for random netlist constant computation"],
    'unmanaged_resets': ['l', 'List of unmanaged external resets']
}

top_added = {
    'alert': ['l', 'alerts'],
    'exported_rsts': ['g', 'external resets grouped by something (TODO)'],
    'incoming_alert': ['g', 'Parsed incoming alerts'],
    'incoming_interrupt': ['g', 'Parsed incoming interrupts'],
    'interrupt': ['l', 'interrupts'],
    'racl': ['g', 'the expansion of the racl_config file'],
    'wakeups':
    ['l', 'list of wakeup requests each holding name, width, and module'],
    'cfg_path': ['s', 'Path to the folder of the toplevel HJSON file']
}

pinmux_required = {
    'enable_usb_wakeup': ['pb', 'Enable USB wakeup in pinmux'],
    'enable_strap_sampling':
    ['pb', 'Enable hardware strap sampling of pinmux']
}
pinmux_optional = {
    'num_wkup_detect': ['d', 'Number of wakeup detectors'],
    'wkup_cnt_width': ['d', 'Number of bits in wakeup detector counters'],
    'signals': ['l', 'List of Dedicated IOs.'],
}
pinmux_added = {
    'ios': ['l', 'Full list of IO'],
    'io_counts': ['g', 'count of ios grouped by dedicated or muxed'],
}

pinmux_sig_required = {
    'instance': ['s', 'Module instance name'],
    'connection': [
        's', 'Specification of connection type, can be direct, manual or '
        'muxed'
    ],
}
pinmux_sig_optional = {
    'port': ['s', 'Port name of module'],
    'pad': ['s', 'Pad name for direct connections'],
    'desc': ['s', 'Signal description'],
    'attr': ['s', 'Pad type for generating the correct attribute CSR']
}
pinmux_sig_added = {}

pinmux_io_required = {
    'name': ['s', 'the name of the io'],
    'width': ['d', 'the bit width of the io'],
    'connection':
    ['s', 'Specification of connection type, can be direct, manual or muxed'],
    'type': ['s', 'input, output, or inout TODO'],
}
pinmux_io_optional = {
    'glob_idx': ['d', 'TODO'],
    'idx': ['d', 'TODO'],
}.update(pinmux_sig_optional)
pinmux_io_added = {}

pinmux_io_count_required = {
    'inouts': ['d', 'the count of inout ios of the io type'],
    'inputs': ['d', 'the count of inout ios of the io type'],
    'outputs': ['d', 'the count of inout ios of the io type'],
    'pads': ['d', 'the count of pads of the io type'],
}
pinmux_io_count_optional = {}
pinmux_io_count_added = {}

pinout_required = {
    'banks': ['l', 'List of IO power banks'],
    'pads': ['l', 'List of pads']
}
pinout_optional = {}
pinout_added = {
    'idx': ['d', 'the index of the pin'],
}

pad_required = {
    'name': ['l', 'Pad name'],
    'type': ['s', 'Pad type'],
    'bank': ['s', 'IO power bank for the pad'],
    'connection': [
        's', 'Specification of connection type, '
        'can be direct, manual or muxed'
    ],
}
pad_optional = {
    'desc': ['s', 'Pad description'],
    'port_type': ['s', 'Special port type other than `inout wire`']
}
pad_added = {
    'idx': ['d', 'the index of the pad'],
}

target_required = {
    'name': ['s', 'Name of target'],
    'pinout': ['g', 'Target-specific pinout configuration'],
    'pinmux': ['g', 'Target-specific pinmux configuration']
}
target_optional = {}
target_added = {}

target_pinmux_required = {
    'special_signals':
    ['l', 'List of special signals and the pad they are mapped to.'],
}
target_pinmux_optional = {}
target_pinmux_added = {}

target_pinout_required = {
    'remove_ports': ['l', 'List of port names to remove from the port list'],
    'remove_pads': ['l', 'List of pad names to remove and stub out'],
    'add_pads': ['l', 'List of manual pads to add'],
}
target_pinout_optional = {}
target_pinout_added = {}

straps_required = {
    'tap0': ['s', 'Name of tap0 pad'],
    'tap1': ['s', 'Name of tap1 pad'],
    'dft0': ['s', 'Name of dft0 pad'],
    'dft1': ['s', 'Name of dft1 pad'],
}
straps_optional = {}
straps_added = {}

straps_required = {
    'tap0': ['s', 'Name of tap0 pad'],
    'tap1': ['s', 'Name of tap1 pad'],
    'dft0': ['s', 'Name of dft0 pad'],
    'dft1': ['s', 'Name of dft1 pad'],
}
straps_optional = {}
straps_added = {}

special_sig_required = {
    'name': ['s', 'DIO name'],
    'pad': ['s', 'Pad name'],
}
special_sig_optional = {
    'desc': ['s', 'Description of signal connection'],
}
special_sig_added = {
    'idx': ['d', 'the index of the signal'],
}

eflash_required = {
    'type': ['s', 'string indicating type of memory'],
    'banks': ['d', 'number of flash banks'],
    'pages_per_bank': ['d', 'number of data pages per flash bank'],
    'program_resolution':
    ['d', 'maximum number of flash words allowed to program'],
}

eflash_optional = {}

eflash_added = {}

module_required = {
    'name': ['s', 'name of the instance'],
    'type': ['s', 'comportable IP type'],
    'clock_srcs': ['g', 'dict with clock sources'],
    'clock_group': ['s', 'clock group'],
    'reset_connections': ['g', 'dict with reset sources'],
}

module_optional = {
    'domain': ['l', 'optional list of power domains, defaults to Domain0'],
    'clock_reset_export': [
        'l', 'optional list with prefixes for exported '
        'clocks and resets at the chip level'
    ],
    'attr': [
        's', 'optional attribute indicating whether the IP is '
        '"ipgen", "reggen_top", or "reggen_only"'
    ],
    'base_addr': [
        'g', 'dict of address space mapped to the corresponding hex start '
        'address of the peripheral (if the IP has only a single TL-UL '
        'interface)'
    ],
    'base_addrs': [
        'g', 'hex start addresses of the peripheral '
        ' (if the IP has multiple TL-UL interfaces)'
    ],
    'memory': ['g', 'optional dict with memory region attributes'],
    'param_decl':
    ['g', 'optional dict that allows to override instantiation parameters'],
    'generate_dif': [
        'pb',
        'optional bool to indicate if a DIF should be generated for that '
        'module'
    ],
    'outgoing_alert': [
        's', 'optional string to indicate alerts are routed externally to '
        'the named group'
    ],
    'outgoing_interrupt': [
        's', 'optional string to indicate interrupts are routed externally to '
        'the named group'
    ],
    'incoming_alert': [
        'l', 'optional list of paths to incoming alert configurations for the '
        'alert_handler'
    ],
    'ipgen_param': ['g', 'Optional ipgen parameters for that instance'],
    'template_type': ['s', 'Base template type of ipgen IPs'],
    'racl_group': [
        's', 'Only valid for racl_ctrl IPs. Defines the RACL group this '
        'control IP is associated to'
    ],
    'racl_mappings':
    ['g', 'dict that maps an interface to its associated RACL mapping'],
    'racl_mapping': [
        's', 'A special case of racl_mappings. If specified, this is taken to '
        'represent a dict that associates all interfaces with the given '
        'mapping. It is an error to specify both this and racl_mappings.'
    ],
}

module_added = {
    'clock_connections': ['g', 'generated clock connections'],
    'incoming_interrupt': ['g', 'Parsed incoming interrupts'],
    'inter_signal_list': ['l', 'generated signal information'],
    'param_list': ['l', 'list of parameters'],
}

memory_required = {
    'label': ['s', 'region label for the linker script'],
    'swaccess': ['s', 'access attributes for the memory region (ro, rw)'],
    'exec': ['pb', 'executable region indication for the linker script'],
    'byte_write':
    ['pb', 'indicate whether the memory supports byte write accesses'],
}

memory_optional = {
    'size': [
        'd', 'memory region size in bytes for the linker script, '
        'xbar and RTL parameterisations'
    ],
    'config': ['d', 'Extra configuration for a particular memory'],
    'data_intg_passthru':
    ['pb', 'Integrity bits are passed through directly from the memory']
}

memory_added = {}

reset_connection_required = {
    'name': ['s', 'name of the connecting reset'],
    'domain': ['s', 'connected domain'],
}

reset_connection_optional = {}
reset_connection_added = {}

reset_requests_required = {}
reset_requests_optional = {
    'int': [
        's', 'internal request list, for example, escalation reset and '
        'power glitches'
    ],
    'debug': [
        's',
        'debug request list, since a different set of resets becomes active'
    ],
    'peripheral': [
        's',
        'peripheral request list, where the reset requests are explicit in '
        'the top config'
    ],
}
reset_requests_added = {}

reset_request_required = {
    'name': ['s', 'the reset request name'],
    'desc': ['s', 'the reset request descrption'],
    'module': ['s', 'the reset request source'],
}
reset_request_optional = {
    'width': ['d', 'TODO'],
}
reset_request_added = {}

wakeup_required = {
    'name': ['s', 'the wakeup name'],
    'width': ['d', 'the width of the signal'],
    'module': ['s', 'the module sourcing the wakeup'],
}
wakeup_optional = {}
wakeup_added = {}

alert_required = {
    'name': ['s', 'name of the alert signal'],
    'width': ['d', 'the number of alerts in this signal, typically 1'],
    'async': ['s', 'string interpreted as boolean'],
    'module_name': ['s', 'The module name of the source'],
}
alert_optional = {
    'desc': ['s', 'the description of the alert'],
    'lpg_name': ['s', 'the low power group of the alert'],
    'lpg_idx': ['d', 'the index in the lpg group'],
    'type': ['s', 'should contain "alert"'],
}
alert_added = {}

interrupt_required = {
    'name': ['s', 'the name of the interrupt'],
    'width': ['d', 'the number of interrupts in this signal, typically 1'],
    'module_name': ['s', 'The module name of the source'],
    'intr_type': ['s', 'The IntrType, either Event or Status'],
    'default_val': ['s', 'a string interpreted as boolean'],
    'incoming': ['s', 'a string interpreted as boolean'],
}
interrupt_optional = {
    'desc': ['s', 'the description of the interrupt'],
    'type': ['s', 'should contain "interrupt"'],
}
interrupt_added = {}

param_required = {
    'name': ['s', 'the parameter name'],
    'desc': ['s', 'the parameter description'],
    'type': ['s', 'the data type of the parameter'],
    'default': ['s', 'the default value of the parameter'],
}
param_optional = {
    'expose': ['s', 'seems redundant TODO'],
    'local': ['s', 'whether it is a localparam, interpreted as boolean'],
    'name_top': ['s', 'the name in the top-level'],
    'randcount': ['d', 'TODO'],
    'randtype': ['s', 'whether it is for "data" or "perm"issions'],
    'randwidth': ['d', 'the number of bits'],
    'unpacked_dimensions': ['s', 'the unpacked dimensions for arrays'],
}
param_added = {}

inter_sig_required = {
    'name': ['s', 'the name of the signal'],
    'struct': ['s', 'the data type of the signal'],
    'type': [
        's',
        'whether the signal is unidirectional or part of a request-response '
        'pair'
    ],
    'act': ['s', 'whether it is a request (req) or a response (rsp)'],
    'width': ['d', 'the number of items of the signal for arrays'],
}
inter_sig_optional = {
    'desc': ['s', 'the inter signal description'],
    'inst_name': ['s', 'the instance this signal connects to'],
    'index': ['d', 'the index when this is connected to an array'],
    'package': ['s', 'the package declaring the struct'],
    'default': ['s', 'TODO'],
    'end_idx': ['d', 'TODO'],
    'top_signame': ['s', 'TODO'],
}
inter_sig_added = {}


# Supported PAD types.
# Needs to coincide with enum definition in prim_pad_wrapper_pkg.sv
class PadType(Enum):
    INPUT_STD = 'InputStd'
    BIDIR_STD = 'BidirStd'
    BIDIR_TOL = 'BidirTol'
    BIDIR_OD = 'BidirOd'
    ANALOG_IN0 = 'AnalogIn0'
    ANALOG_IN1 = 'AnalogIn1'
    DUAL_BIDIR_TOL = 'DualBidirTol'


def is_valid_pad_type(obj):
    try:
        PadType(obj)
    except ValueError:
        return False
    return True


class TargetType(Enum):
    MODULE = "module"
    XBAR = "xbar"


class Target:
    """Target class informs the checkers if we are validating a module or xbar
    """

    def __init__(self, target_type):
        # The type of this target
        self.target_type = target_type
        # The key to search against
        if target_type == TargetType.MODULE:
            self.key = "type"
        else:
            self.key = "name"


class Flash:
    """Flash class contains information regarding parameter defaults.
       For now, only expose banks / pages_per_bank for user configuration.
       For now, also enforce power of 2 requiremnt.
    """
    max_banks = 4
    max_pages_per_bank = 1024

    def __init__(self, mem, base_addrs):
        self.base_addrs = {
            asid: int(base, 16)
            for (asid, base) in base_addrs.items()
        }
        self.banks = mem.get('banks', 2)
        self.pages_per_bank = mem.get('pages_per_bank', 8)
        self.program_resolution = mem.get('program_resolution', 128)
        self.words_per_page = 256
        self.data_width = 64
        self.metadata_width = 12
        self.info_types = 3
        self.infos_per_bank = [10, 1, 2]
        self.word_bytes = int(self.data_width / 8)
        self.pgm_resolution_bytes = int(self.program_resolution *
                                        self.word_bytes)
        self.check_values()

        # populate size variable
        self.bytes_per_page = self.word_bytes * self.words_per_page
        self.bytes_per_bank = self.bytes_per_page * self.pages_per_bank

        size_int = int(self.bytes_per_bank * self.banks)
        self.size = hex(size_int)

    def is_pow2(self, n):
        return (n != 0) and (n & (n - 1) == 0)

    def check_values(self):
        pow2_check = (self.is_pow2(self.banks) and
                      self.is_pow2(self.pages_per_bank) and
                      self.is_pow2(self.program_resolution))
        limit_check = ((self.banks <= Flash.max_banks) and
                       (self.pages_per_bank <= Flash.max_pages_per_bank))

        if not pow2_check:
            raise ValueError(
                'flash power of 2 check failed. A supplied parameter '
                'is not power of 2')

        if not limit_check:
            raise ValueError(
                'flash number of banks and pages per bank too large')

    def _asdict(self):
        return {
            'banks': self.banks,
            'pages_per_bank': self.pages_per_bank,
            'program_resolution': self.program_resolution,
            'pgm_resolution_bytes': self.pgm_resolution_bytes,
            'bytes_per_page': self.bytes_per_page,
            'bytes_per_bank': self.bytes_per_bank,
            'size': self.size
        }


# Check to see if each module/xbar defined in top.hjson exists as ip/xbar.hjson
# Also check there are not multiple definitions of ip/xbar.hjson for each top
# level definition
# If it does, return a dictionary of instance names to index in ip/xbarobjs
def check_target(top, name_to_block, tgtobj):
    error = 0

    tgt_type = tgtobj.target_type.value
    inst_key = tgtobj.key

    for cfg in top[tgt_type]:
        cfg_name = cfg['name'].lower()
        log.info("Checking target %s %s" % (tgt_type, cfg_name))

        if cfg[inst_key] not in name_to_block:
            log.error(f"Could not find ip_block for {cfg_name}")
            error += 1

    return error


def check_pad(top: ConfigT, pad: Dict, known_pad_names: Dict,
              valid_connections: List[str], prefix: str) -> int:
    error = 0
    error += check_keys(pad, pad_required, pad_optional, pad_added, prefix)

    # check name uniqueness
    if pad['name'] in known_pad_names:
        log.warning('Pad name {} is not unique'.format(pad['name']))
        error += 1
    known_pad_names[pad['name']] = 1

    if not is_valid_pad_type(pad['type']):
        log.warning('Unkown pad type {}'.format(pad['type']))
        error += 1

    if pad['bank'] not in top['pinout']['banks']:
        log.warning('Unkown io power bank {}'.format(pad['bank']))
        error += 1

    if pad['connection'] not in valid_connections:
        log.warning('Connection type {} of pad {} is invalid'.format(
            pad['connection'], pad['name']))
        error += 1

    pad.setdefault('port_type', 'inout')

    return error


def check_alerts(top: ConfigT, prefix: str) -> int:
    if 'alert' not in top:
        return 0
    error = 0
    for alert in top['alert']:
        error += check_keys(alert, alert_required, alert_optional, alert_added,
                            prefix + ' Alert')
    return error


def check_incoming_alerts(top: ConfigT, prefix: str) -> int:
    if 'incoming_alert' not in top:
        return 0
    error = 0
    # TODO
    return error


def check_outgoing_alerts(top: ConfigT, prefix: str) -> int:
    if 'outgoing_alert' not in top:
        return 0
    error = 0
    # TODO
    return error


def check_outgoing_interrupts(top: ConfigT, prefix: str) -> int:
    if "outgoing_interrupt" not in top:
        return 0
    error = 0
    # TODO
    return error


def check_interrupts(top: ConfigT, prefix: str) -> int:
    if 'interrupt' not in top:
        return 0
    error = 0
    for interrupt in top['interrupt']:
        error += check_keys(interrupt, interrupt_required, interrupt_optional,
                            interrupt_added, prefix + ' Interrupt')
    return error


def check_incoming_interrupts(top: ConfigT, prefix: str) -> int:
    error = 0
    # TODO
    return error


def check_pinout(top: ConfigT, prefix: str) -> int:
    error = check_keys(top['pinout'], pinout_required, pinout_optional,
                       pinout_added, prefix + ' Pinout')

    known_names = {}
    for pad in top['pinout']['pads']:
        error += check_keys(pad, pad_required, pad_optional, pad_added,
                            prefix + ' Pinout')

        error += check_pad(top, pad, known_names,
                           ['direct', 'manual', 'muxed'], prefix + ' Pad')

    return error


def check_pinmux(top: ConfigT, prefix: str) -> int:
    error = check_keys(top['pinmux'], pinmux_required, pinmux_optional,
                       pinmux_added, prefix + ' Pinmux')

    # This is used for the direct connection accounting below,
    # where we tick off already connected direct pads.
    known_direct_pads = {}
    direct_pad_attr = {}
    for pad in top['pinout']['pads']:
        if pad['connection'] == 'direct':
            known_direct_pads[pad['name']] = 1
            direct_pad_attr[pad['name']] = pad['type']

    # Note: the actual signal crosscheck is deferred until the merge stage,
    # since we have no idea at this point which IOs comportable IPs expose.
    for sig in top['pinmux']['signals']:
        error += check_keys(sig, pinmux_sig_required, pinmux_sig_optional,
                            pinmux_sig_added, prefix + ' Pinmux signal')

        if sig['connection'] not in ['direct', 'manual', 'muxed']:
            log.warning(f'Invalid connection type {sig["connection"]}')
            error += 1

        # The pad needs to refer to a valid pad name in the pinout that is of
        # connection type "direct". We tick off all direct pads that have been
        # referenced in order to make sure there are no double connections
        # and unconnected direct pads.
        padname = sig.setdefault('pad', '')
        if padname != '':
            if padname in known_direct_pads:
                if known_direct_pads[padname] == 1:
                    known_direct_pads[padname] = 0
                    padattr = direct_pad_attr[padname]
                else:
                    log.warning(
                        f'Warning, direct pad {padname} is already connected')
                    error += 1
            else:
                log.warning('Unknown direct pad {}'.format(padname))
                error += 1

        # Check port naming scheme.
        port = sig.setdefault('port', '')
        pattern = r'^[a-zA-Z0-9_]*(\[[0-9]*\]){0,1}'
        matches = re.match(pattern, port)
        if matches is None:
            log.warning(f'Port name {port} has wrong format')
            error += 1

        # Check that only direct connections have pad keys
        if sig['connection'] == 'direct':
            if 'attr' in sig and sig['attr'] != padattr:
                log.warning(
                    'Direct connection of instance {} port {} pad attribute '
                    '{} does not match expected {}'.format(
                        sig['instance'], sig['port'], sig['attr'], padattr))
                error += 1
            # Since the signal is directly connected, we can automatically
            # infer the pad type needed to instantiate the correct attribute
            # CSR WARL module inside the pinmux.
            sig['attr'] = padattr

            if padname == '':
                log.warning(
                    'Instance {} port {} connection is of direct type and '
                    'therefore must have an associated pad name.'.format(
                        sig['instance'], sig['port']))
                error += 1
            if port == '':
                log.warning(
                    'Instance {} port {} connection is of direct type and '
                    'therefore must have an associated port name.'.format(
                        sig['instance'], sig['port']))
                error += 1
        elif sig['connection'] == 'muxed':
            # Muxed signals do not have a corresponding pad and attribute CSR,
            # since they first go through the pinmux matrix.
            if sig.setdefault('attr', '') != '':
                log.warning(
                    'Muxed connection of instance {} port {} must not have '
                    'an associated pad attribute field'.format(
                        sig['instance'], sig['port']))
                error += 1
            if padname != '':
                log.warning('Muxed connection of instance {} port {} '
                            'must not have an associated pad'.format(
                                sig['instance'], sig['port']))
                error += 1
        elif sig['connection'] == 'manual':
            # This pad attr key is only allowed in the manual case,
            # as there is no way to infer the pad type automatically.
            sig.setdefault('attr', 'BidirStd')
            if padname != '':
                log.warning('Manual connection of instance {} port {} '
                            'must not have an associated pad'.format(
                                sig['instance'], sig['port']))
                error += 1

    # At this point, all direct pads should have been ticked off.
    for key, val in known_direct_pads.items():
        if val == 1:
            log.warning('Direct pad {} has not been connected'.format(key))
            error += 1

    # Check added ios
    for io in top.get('ios', []):
        error += check_keys(io, pinmux_io_required, pinmux_io_optional,
                            pinmux_io_added, f'{prefix} Pinmux ios')

    # Check added io_counts
    for k, counts in top.get('io_counts', {}).items():
        if k not in ['dedicated', 'muxed']:
            log.error(f'{prefix} Pinmux io counts unexpected key {k}')
            error += 1
        for count in counts:
            error += check_keys(count, pinmux_io_count_required,
                                pinmux_io_count_optional,
                                pinmux_io_count_added,
                                f'{prefix} Pinmux io {k} counts')
    return error


def check_implementation_targets(top: ConfigT, prefix: str) -> int:
    error = 0
    known_names = {}
    for target in top['targets']:
        error += check_keys(target, target_required, target_optional,
                            target_added, prefix + ' Targets')

        # check name uniqueness
        if target['name'] in known_names:
            log.warning('Target name {} is not unique'.format(target['name']))
            error += 1
        known_names[target['name']] = 1

        error += check_keys(target['pinmux'], target_pinmux_required,
                            target_pinmux_optional, target_pinmux_added,
                            prefix + ' Target pinmux')

        error += check_keys(target['pinout'], target_pinout_required,
                            target_pinout_optional, target_pinout_added,
                            prefix + ' Target pinout')

        # Check special pad signals
        known_entry_names = {}
        for entry in target['pinmux']['special_signals']:
            error += check_keys(entry, special_sig_required,
                                special_sig_optional, special_sig_added,
                                prefix + ' Special signal')

            # check name uniqueness
            if entry['name'] in known_entry_names:
                log.warning('Special pad name {} is not unique'.format(
                    entry['name']))
                error += 1
            known_entry_names[entry['name']] = 1

            # The pad key needs to refer to a valid pad name.
            is_muxed = False
            for pad in top['pinout']['pads']:
                if entry['pad'] == pad['name']:
                    is_muxed = pad['connection'] == 'muxed'
                    break
            else:
                log.warning('Unknown pad {}'.format(entry['pad']))
                error += 1

            if not is_muxed:
                # If this is not a muxed pad, we need to make sure this refers
                # to DIO that is NOT a manual pad.
                for sig in top['pinmux']['signals']:
                    if entry['pad'] == sig['pad']:
                        break
                else:
                    log.warning(
                        'Special pad {} cannot refer to a manual pad'.format(
                            entry['pad']))
                    error += 1

        # Check ports to remove
        for entry in target['pinout']['remove_ports']:
            # The pad key needs to refer to a valid pad name.
            for pad in top['pinout']['pads'] + target['pinout']['add_pads']:
                if entry == pad['name']:
                    break
            else:
                log.warning('Unknown pad {}'.format(entry))
                error += 1

        # Check pads to remove and stub out
        for entry in target['pinout']['remove_pads']:
            # The pad key needs to refer to a valid pad name.
            for pad in top['pinout']['pads']:
                if entry == pad['name']:
                    break
            else:
                log.warning('Unknown pad {}'.format(entry))
                error += 1

        # Check pads to add
        known_pad_names = {}
        for pad in top['pinout']['pads']:
            known_pad_names.update({pad['name']: 1})

        for pad in target['pinout']['add_pads']:
            error += check_pad(top, pad, known_pad_names, ['manual'],
                               prefix + ' Additional Pad')

    return error


def check_clocks_resets(top: ConfigT, ip_name_to_block: IpBlocksT,
                        xbar_name_to_block: IpBlocksT) -> int:

    error = 0

    # all defined clock/reset nets
    if isinstance(top['resets'], Resets):
        reset_nets = [reset.name for reset in top['resets'].nodes.values()]
    else:
        reset_nets = [reset['name'] for reset in top['resets']['nodes']]
    clock_srcs = list(top['clocks'].all_srcs.keys())
    unmanaged_clock_srcs = list(top['unmanaged_clocks'].clks.keys())
    unmanaged_resets = top.get('unmanaged_resets')
    if unmanaged_resets:
        if isinstance(unmanaged_resets, UnmanagedResets):
            unmanaged_reset_nets = [
                reset for reset in unmanaged_resets.resets.keys()
            ]
        else:
            unmanaged_reset_nets = [
                net for reset in unmanaged_resets for net in reset.values()
            ]

    # Check clock/reset port connection for all IPs
    for ipcfg in top['module']:
        ipcfg_name = ipcfg['type']
        log.info("Checking clock/resets for %s" % ipcfg_name)
        error += validate_reset(ipcfg, ip_name_to_block[ipcfg_name],
                                reset_nets, unmanaged_reset_nets)
        error += validate_clock(ipcfg, ip_name_to_block[ipcfg_name],
                                clock_srcs, unmanaged_clock_srcs)

        if error:
            log.error("module clock/reset checking failed")
            break

    # Check clock/reset port connection for all xbars
    for xbarcfg in top['xbar']:
        xbarcfg_name = xbarcfg['name'].lower()
        log.info("Checking clock/resets for xbar %s" % xbarcfg_name)
        error += validate_reset(xbarcfg, xbar_name_to_block[xbarcfg_name],
                                reset_nets, unmanaged_reset_nets, "xbar")
        error += validate_clock(xbarcfg, xbar_name_to_block[xbarcfg_name],
                                clock_srcs, unmanaged_clock_srcs, "xbar")

        if error:
            log.error("xbar clock/reset checking failed")
            break

    return error


def check_reset_requests(top: ConfigT, component: str) -> int:
    error = 0
    for key, resets in top.get('reset_requests', {}).items():
        all_keys = [
            k for d in [
                reset_requests_required, reset_requests_optional,
                reset_requests_added
            ] for k in d.keys()
        ]
        if key not in all_keys:
            log.error(f'unknown key {key} in {component} Reset requests')
            error += 1
        for reset_req in resets:
            error += check_keys(reset_req, reset_request_required,
                                reset_request_optional, reset_request_added,
                                f'{component} Reset request')
    return error


def check_exported_resets(top: ConfigT, component: str) -> int:
    error = 0
    for key, resets in top.get('exported_rsts', {}).items():
        # TODO
        pass
    return error


def check_wakeups(top: ConfigT, component: str) -> int:
    error = 0
    for wakeup in top.get('wakeups', []):
        error += check_keys(wakeup, wakeup_required, wakeup_optional,
                            wakeup_added, f'{component} Wakeups')
    return error


# Checks the following
# - For each defined reset connection in top*.hjson, there exists a defined
#   port at the destination and defined reset net
# - There are the same number of defined connections as there are ports
def validate_reset(top: ConfigT,
                   inst: Union[IpBlock, ConfigT],
                   reset_nets: List[str],
                   unmanaged_reset_nets: List[str],
                   prefix="") -> int:
    # Gather inst port list
    error = 0

    # Handle either an IpBlock (generated by reggen) or an OrderedDict
    # (generated by topgen for a crossbar)
    if isinstance(inst, IpBlock):
        name = inst.name
        reset_signals = inst.clocking.reset_signals()
    else:
        name = inst['name']
        reset_signals = ([inst.get('reset_primary', 'rst_ni')] +
                         inst.get('other_reset_list', []))

    log.info(f"{prefix} {name} resets are {reset_signals}")

    # Check if reset connections are properly formatted
    # There are two options
    # The reset connection for a particular port must be a str
    # The reset connection for a particular port must be a dict
    # If value is a string, the module can only have ONE domain
    # If value is a dict, it must have the keys name / domain, and the
    # value of domain must match that defined for the module.
    for port, reset in top["reset_connections"].items():
        if isinstance(reset, str):
            top["reset_connections"][port] = {}
            top["reset_connections"][port]['name'] = reset

            if len(top["domain"]) > 1:
                raise ValueError(f"{top['name']} reset connection {reset} "
                                 "has no assigned domain")
            else:
                top["reset_connections"][port]['domain'] = top["domain"][0]

        if isinstance(reset, dict):
            error += check_keys(reset, reset_connection_required,
                                reset_connection_optional,
                                reset_connection_added,
                                'dict structure for reset connections')

            if reset['domain'] not in top["domain"]:
                error += 1
                log.error(f"domain {reset['domain']} defined for reset "
                          f"{reset['name']} is not a domain of {top['name']}")

    # Check if the reset connections are fully populated
    if len(top['reset_connections']) != len(reset_signals):
        error += 1
        log.error(f"{prefix} {name} mismatched number of reset ports and nets")

    missing_port = [
        port for port in top['reset_connections'].keys()
        if port not in reset_signals
    ]

    if missing_port:
        error += 1
        log.error(f"{prefix} {name} Following reset ports do not exist:")
        [log.error(f"{port}") for port in missing_port]

    missing_net = [
        net['name'] for net in top['reset_connections'].values()
        if net['name'] not in reset_nets + unmanaged_reset_nets
    ]

    if missing_net:
        error += 1
        log.error(f"{prefix} {name} Following reset nets do not exist:")
        [log.error(f"{net}") for net in missing_net]

    return error


# Checks the following
# - For each defined clock_src in top*.hjson, there exists a defined port at
#   the destination and defined clock source
# - There are the same number of defined connections as there are ports
def validate_clock(top: ConfigT,
                   inst: Union[IpBlock, ConfigT],
                   clock_srcs: List[str],
                   unmanaged_clock_srcs: List[str],
                   prefix="") -> int:
    # Gather inst port list
    error = 0

    # Handle either an IpBlock (generated by reggen) or an OrderedDict
    # (generated by topgen for a crossbar)
    if isinstance(inst, IpBlock):
        name = inst.name
        clock_signals = inst.clocking.clock_signals(False)
    else:
        name = inst['name']
        clock_signals = ([inst.get('clock_primary', 'rst_ni')] +
                         inst.get('other_clock_list', []))

    if len(top['clock_srcs']) != len(clock_signals):
        error += 1
        log.error(f"{prefix} {name} mismatched number of clock ports and nets")

    missing_port = [
        port for port in top['clock_srcs'].keys() if port not in clock_signals
    ]

    if missing_port:
        error += 1
        log.error(f"{prefix} {name} Following clock ports do not exist:")
        [log.error(f"{port}") for port in missing_port]

    missing_net = []
    for port, net in top['clock_srcs'].items():
        net_name = net['clock'] if isinstance(net, Dict) else net

        if net_name not in clock_srcs and net_name not in unmanaged_clock_srcs:
            missing_net.append(net)

    if missing_net:
        error += 1
        log.error(f"{prefix} {name} Following clock nets do not exist:")
        [log.error(f"{net}") for net in missing_net]

    return error


def check_flash(top: ConfigT):

    for mem in top['memory']:
        if mem['type'] == "eflash":

            raise ValueError(
                'top level flash memory definition not supported. Please use '
                'the flash embedded inside flash_ctrl instead.  If there is a '
                'need for top level flash memory, please file an issue.')


def check_power_domains(top: ConfigT):

    # check that the default domain is valid
    if top['power']['default'] not in top['power']['domains']:
        raise ValueError(f"Default power domain {top['power']['default']} is "
                         "not a valid domain")

    # Check that each module, xbar, memory has a power domain defined.
    # If not, give it a default.
    # If there is one defined, check that it is a valid definition
    for end_point in top['module'] + top['memory'] + top['xbar']:
        if 'domain' not in end_point:
            end_point['domain'] = [top['power']['default']]

        for d in end_point['domain']:
            if d not in top['power']['domains']:
                raise ValueError(
                    f"{end_point['name']} defined invalid domain {d}")


def check_modules(top: ConfigT, prefix: str) -> int:
    error = 0
    for m in top['module']:
        modname = m.get("name", "unnamed module")
        error += check_keys(m, module_required, module_optional, module_added,
                            prefix + " " + modname)

        # these fields are mutually exclusive
        if 'base_addr' in m and 'base_addrs' in m:
            log.error("{} {} a module cannot define both the 'base_addr' "
                      "and 'base_addrs' keys at the same time".format(
                          prefix, modname))
            error += 1

        if 'base_addrs' in m and 'memory' in m:
            for intf, value in m['memory'].items():
                error += check_keys(value, memory_required, memory_optional,
                                    memory_added,
                                    prefix + " " + modname + " " + intf)

                # if size is not declared, there must be extra config to
                # determine it
                if 'size' not in value and 'config' not in value:
                    raise ValueError(
                        f'{m["name"]} memory declaration has neither size '
                        'nor extra configuration.  Unable to determine '
                        'memory size')

                # check the memory regions correspond to the TL-UL interfaces
                if intf not in m['base_addrs']:
                    raise ValueError(
                        f'{prefix} {modname} memory region {intf} does not '
                        'correspond to any of the defined TL-UL interfaces')

                if 'size' not in value:
                    mem_type = value['config'].get('type', "")

                    if mem_type == "flash":
                        check_keys(value['config'], eflash_required,
                                   eflash_optional, eflash_added, "Eflash")
                        flash = Flash(value['config'], m['base_addrs'][intf])
                        value['size'] = flash.size
                        value['config'] = flash
                    else:
                        raise ValueError(
                            f'{m["name"]} memory config declaration does not '
                            'have a valid type')

                # make sure the linker region access attribute is valid
                attr = value.get('swaccess', 'unknown attribute')
                if attr not in ['ro', 'rw']:
                    log.error(
                        '{} {} swaccess attribute {} of memory region {} '
                        'is not valid'.format(prefix, modname, attr, intf))
                    error += 1
        if 'inter_signal_list' in m:
            for sig in m['inter_signal_list']:
                sig_name = sig.get('name', 'no name')
                error += check_keys(sig, inter_sig_required,
                                    inter_sig_optional, inter_sig_added,
                                    f"{modname} Inter signal {sig_name}")
        if 'param_list' in m:
            for param in m['param_list']:
                param_name = param.get('name', 'no name')
                error += check_keys(param, param_required, param_optional,
                                    param_added,
                                    f"{modname} Parameter {param_name}")
    return error


def validate_top(top: ConfigT, ip_name_to_block: IpBlocksT,
                 xbar_name_to_block: IpBlocksT) -> int:
    # return as it is for now
    error = check_keys(top, top_required, top_optional, top_added, "top")

    if error != 0:
        log.error("Top HJSON has top level errors. Aborting")
        return top, error

    component = top['name']

    # Check module instantiations
    error += check_modules(top, component)

    # MODULE  check
    error += check_target(top, ip_name_to_block, Target(TargetType.MODULE))

    # XBAR check
    error += check_target(top, xbar_name_to_block, Target(TargetType.XBAR))

    # MEMORY check
    check_flash(top)

    # Power domain check
    check_power_domains(top)

    error += check_reset_requests(top, component)
    error += check_exported_resets(top, component)
    error += check_wakeups(top, component)

    # Clock / Reset check
    error += check_clocks_resets(top, ip_name_to_block, xbar_name_to_block)

    # RV_PLIC check

    # Pinout, pinmux and target checks
    # Note that these checks must happen in this order, as
    # the pinmux and target configs depend on the pinout.
    error += check_pinout(top, component)
    error += check_pinmux(top, component)
    error += check_implementation_targets(top, component)

    error += check_alerts(top, component)
    error += check_incoming_alerts(top, component)
    error += check_outgoing_alerts(top, component)
    error += check_outgoing_interrupts(top, component)
    error += check_interrupts(top, component)
    error += check_incoming_interrupts(top, component)

    return top, error
