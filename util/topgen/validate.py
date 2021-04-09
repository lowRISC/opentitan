# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
import re
import logging as log
from collections import OrderedDict
from enum import Enum
from typing import Dict, List

from reggen.validate import check_keys
from reggen.ip_block import IpBlock

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
    'module': ['l', 'list of modules to instantiate'],
    'memory': ['l', 'list of memories. At least one memory '
                    'is needed to run the software'],
    'debug_mem_base_addr': ['d', 'Base address of RV_DM. '
                                 'Planned to move to module'],
    'xbar': ['l', 'List of the xbar used in the top'],
    'rnd_cnst_seed': ['int', "Seed for random netlist constant computation"],
    'pinout': ['g', 'Pinout configuration'],
    'targets': ['l', ' Target configurations'],
    'pinmux': ['g', 'pinmux configuration'],
}

top_optional = {
    'alert_async': ['l', 'async alerts (generated)'],
    'alert': ['lnw', 'alerts (generated)'],
    'alert_module': [
        'l',
        'list of the modules that connects to alert_handler'
    ],
    'datawidth': ['pn', "default data width"],
    'exported_clks': ['g', 'clock signal routing rules'],
    'host': ['g', 'list of host-only components in the system'],
    'inter_module': ['g', 'define the signal connections between the modules'],
    'interrupt': ['lnw', 'interrupts (generated)'],
    'interrupt_module': ['l', 'list of the modules that connects to rv_plic'],
    'num_cores': ['pn', "number of computing units"],
    'power': ['g', 'power domains supported by the design'],
    'port': ['g', 'assign special attributes to specific ports']
}

top_added = {}

pinmux_required = {}
pinmux_optional = {
    'num_wkup_detect': [
        'd', 'Number of wakeup detectors'
    ],
    'wkup_cnt_width': [
        'd', 'Number of bits in wakeup detector counters'
    ],
    'signals': ['l', 'List of Dedicated IOs.'],
}
pinmux_added = {
    'ios': ['l', 'Full list of IO'],
}

pinmux_sig_required = {
    'instance': ['s', 'Module instance name'],
    'connection': ['s', 'Specification of connection type, '
                        'can be direct, manual or muxed'],
}
pinmux_sig_optional = {
    'port': ['s', 'Port name of module'],
    'pad': ['s', 'Pad name for direct connections'],
    'desc': ['s', 'Signal description'],
    'attr': ['s', 'Pad type for generating the correct attribute CSR']
}
pinmux_sig_added = {}

pinout_required = {
    'banks': ['l', 'List of IO power banks'],
    'pads': ['l', 'List of pads']
}
pinout_optional = {
}
pinout_added = {}

pad_required = {
    'name': ['l', 'Pad name'],
    'type': ['s', 'Pad type'],
    'bank': ['s', 'IO power bank for the pad'],
    'connection': ['s', 'Specification of connection type, '
                        'can be direct, manual or muxed'],
}
pad_optional = {
    'desc': ['s', 'Pad description'],
}
pad_added = {}

target_required = {
    'name': ['s', 'Name of target'],
    'pinout': ['g', 'Target-specific pinout configuration'],
    'pinmux': ['g', 'Target-specific pinmux configuration']
}
target_optional = {
}
target_added = {}

target_pinmux_required = {
    'special_signals': ['l', 'List of special signals and the pad they are mapped to.'],
}
target_pinmux_optional = {}
target_pinmux_added = {}

target_pinout_required = {
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
special_sig_added = {}

clock_srcs_required = {
    'name': ['s', 'name of clock group'],
    'aon': ['s', 'yes, no. aon attribute of a clock'],
    'freq': ['s', 'frequency of clock in Hz'],
}

clock_srcs_optional = {
    'derived': ['s', 'whether clock is derived'],
    'params': ['s', 'extra clock parameters']
}

derived_clock_srcs_required = {
    'name': ['s', 'name of clock group'],
    'aon': ['s', 'yes, no. aon attribute of a clock'],
    'freq': ['s', 'frequency of clock in Hz'],
    'src': ['s', 'source clock'],
    'div': ['d', 'ratio between source clock and derived clock'],
}

clock_groups_required = {
    'name': ['s', 'name of clock group'],
    'src': ['s', 'yes, no. This clock group is directly from source'],
    'sw_cg': ['s', 'yes, no, hint. Software clock gate attributes'],
}
clock_groups_optional = {
    'unique': ['s', 'whether clocks in the group are unique'],
    'clocks': ['g', 'groups of clock name to source'],
}
clock_groups_added = {}

eflash_required = {
    'banks': ['d', 'number of flash banks'],
    'base_addr': ['s', 'strarting hex address of memory'],
    'clock_connections': ['g', 'generated, elaborated version of clock_srcs'],
    'clock_group': ['s', 'associated clock attribute group'],
    'clock_srcs': ['g', 'clock connections'],
    'inter_signal_list': ['lg', 'intersignal list'],
    'name': ['s', 'name of flash memory'],
    'pages_per_bank': ['d', 'number of data pages per flash bank'],
    'program_resolution': ['d', 'maximum number of flash words allowed to program'],
    'reset_connections': ['g', 'reset connections'],
    'swaccess': ['s', 'software accessibility'],
    'type': ['s', 'type of memory']
}

eflash_optional = {}

eflash_added = {}


# Supported PAD types.
# Needs to coincide with enum definition in prim_pad_wrapper_pkg.sv
class PadType(Enum):
    INPUT_STD = 'InputStd'
    BIDIR_STD = 'BidirStd'
    BIDIR_TOL = 'BidirTol'
    BIDIR_OD = 'BidirOd'
    ANALOG_IN0 = 'AnalogIn0'


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

    def __init__(self, mem):
        self.banks = mem['banks']
        self.pages_per_bank = mem['pages_per_bank']
        self.program_resolution = mem['program_resolution']
        self.words_per_page = 256
        self.data_width = 64
        self.metadata_width = 12
        self.info_types = 3
        self.infos_per_bank = [10, 1, 2]

    def is_pow2(self, n):
        return (n != 0) and (n & (n - 1) == 0)

    def check_values(self):
        pow2_check = (self.is_pow2(self.banks) and
                      self.is_pow2(self.pages_per_bank) and
                      self.is_pow2(self.program_resolution))
        limit_check = ((self.banks <= Flash.max_banks) and
                       (self.pages_per_bank <= Flash.max_pages_per_bank))

        return pow2_check and limit_check

    def calc_size(self):
        word_bytes = self.data_width / 8
        bytes_per_page = word_bytes * self.words_per_page
        bytes_per_bank = bytes_per_page * self.pages_per_bank
        return bytes_per_bank * self.banks

    def populate(self, mem):
        mem['words_per_page'] = self.words_per_page
        mem['data_width'] = self.data_width
        mem['metadata_width'] = self.metadata_width
        mem['info_types'] = self.info_types
        mem['infos_per_bank'] = self.infos_per_bank
        mem['size'] = hex(int(self.calc_size()))

        word_bytes = self.data_width / 8
        mem['pgm_resolution_bytes'] = int(self.program_resolution * word_bytes)


# Check to see if each module/xbar defined in top.hjson exists as ip/xbar.hjson
# Also check to make sure there are not multiple definitions of ip/xbar.hjson for each
# top level definition
# If it does, return a dictionary of instance names to index in ip/xbarobjs
def check_target(top, objs, tgtobj):
    error = 0
    idxs = OrderedDict()

    # Collect up counts of object names. We support entries of objs that are
    # either dicts (for top-levels) or IpBlock objects.
    name_indices = {}
    for idx, obj in enumerate(objs):
        if isinstance(obj, IpBlock):
            name = obj.name.lower()
        else:
            name = obj['name'].lower()

        log.info("%d Order is %s" % (idx, name))
        name_indices.setdefault(name, []).append(idx)

    tgt_type = tgtobj.target_type.value
    inst_key = tgtobj.key

    for cfg in top[tgt_type]:
        cfg_name = cfg['name'].lower()
        log.info("Checking target %s %s" % (tgt_type, cfg_name))

        indices = name_indices.get(cfg[inst_key], [])
        if not indices:
            log.error("Could not find %s.hjson" % cfg_name)
            error += 1
        elif len(indices) > 1:
            log.error("Duplicate %s.hjson" % cfg_name)
            error += 1
        else:
            idxs[cfg_name] = indices[0]

    log.info("Current state %s" % idxs)
    return error, idxs


def check_pad(top: Dict,
              pad: Dict,
              known_pad_names: Dict,
              valid_connections: List[str],
              prefix: str) -> int:
    error = 0
    error += check_keys(pad, pad_required, pad_optional,
                        pad_added, prefix)

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
        log.warning('Connection type {} of pad {} is invalid'
                    .format(pad['connection'], pad['name']))
        error += 1

    return error


def check_pinout(top: Dict, prefix: str) -> int:
    error = check_keys(top['pinout'], pinout_required, pinout_optional,
                       pinout_added, prefix + ' Pinout')

    known_names = {}
    for pad in top['pinout']['pads']:
        error += check_keys(pad, pad_required, pad_optional,
                            pad_added, prefix + ' Pinout')

        error += check_pad(top, pad, known_names,
                           ['direct', 'manual', 'muxed'],
                           prefix + ' Pad')

    return error


def check_pinmux(top: Dict, prefix: str) -> int:
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
            log.warning('Invalid connection type {}'.format(sig['connection']))
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
                    log.warning('Warning, direct pad {} is already connected'
                                .format(padname))
                    error += 1
            else:
                log.warning('Unknown direct pad {}'.format(padname))
                error += 1

        # Check port naming scheme.
        port = sig.setdefault('port', '')
        pattern = r'^[a-zA-Z0-9_]*(\[[0-9]*\]){0,1}'
        matches = re.match(pattern, port)
        if matches is None:
            log.warning('Port name {} has wrong format'
                        .format(port))
            error += 1

        # Check that only direct connections have pad keys
        if sig['connection'] == 'direct':
            if sig.setdefault('attr', '') != '':
                log.warning('Direct connection of instance {} port {} '
                            'must not have an associated pad attribute field'
                            .format(sig['instance'],
                                    sig['port']))
                error += 1
            # Since the signal is directly connected, we can automatically infer
            # the pad type needed to instantiate the correct attribute CSR WARL
            # module inside the pinmux.
            sig['attr'] = padattr

            if padname == '':
                log.warning('Instance {} port {} connection is of direct type '
                            'and therefore must have an associated pad name.'
                            .format(sig['instance'],
                                    sig['port']))
                error += 1
            if port == '':
                log.warning('Instance {} port {} connection is of direct type '
                            'and therefore must have an associated port name.'
                            .format(sig['instance'],
                                    sig['port']))
                error += 1
        elif sig['connection'] == 'muxed':
            # Muxed signals do not have a corresponding pad and attribute CSR,
            # since they first go through the pinmux matrix.
            if sig.setdefault('attr', '') != '':
                log.warning('Muxed connection of instance {} port {} '
                            'must not have an associated pad attribute field'
                            .format(sig['instance'],
                                    sig['port']))
                error += 1
            if padname != '':
                log.warning('Muxed connection of instance {} port {} '
                            'must not have an associated pad'
                            .format(sig['instance'],
                                    sig['port']))
                error += 1
        elif sig['connection'] == 'manual':
            # This pad attr key is only allowed in the manual case,
            # as there is no way to infer the pad type automatically.
            sig.setdefault('attr', 'BidirStd')
            if padname != '':
                log.warning('Manual connection of instance {} port {} '
                            'must not have an associated pad'
                            .format(sig['instance'],
                                    sig['port']))
                error += 1

    # At this point, all direct pads should have been ticked off.
    for key, val in known_direct_pads.items():
        if val == 1:
            log.warning('Direct pad {} has not been connected'
                        .format(key))
            error += 1

    return error


def check_implementation_targets(top: Dict, prefix: str) -> int:
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

        error += check_keys(target['pinmux'], target_pinmux_required, target_pinmux_optional,
                            target_pinmux_added, prefix + ' Target pinmux')

        error += check_keys(target['pinout'], target_pinout_required, target_pinout_optional,
                            target_pinout_added, prefix + ' Target pinout')

        # Check special pad signals
        known_entry_names = {}
        for entry in target['pinmux']['special_signals']:
            error += check_keys(entry, special_sig_required, special_sig_optional,
                                special_sig_added, prefix + ' Special signal')

            # check name uniqueness
            if entry['name'] in known_entry_names:
                log.warning('Special pad name {} is not unique'.format(entry['name']))
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
                # If this is not a muxed pad, we need to make sure this refers to
                # DIO that is NOT a manual pad.
                for sig in top['pinmux']['signals']:
                    if entry['pad'] == sig['pad']:
                        break
                else:
                    log.warning('Special pad {} cannot refer to a manual pad'.format(entry['pad']))
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


# check for inconsistent clock group definitions
def check_clock_groups(top):

    # default empty assignment
    if "groups" not in top['clocks']:
        top['clocks']['groups'] = []

    error = 0
    for group in top['clocks']['groups']:
        error = check_keys(group, clock_groups_required, clock_groups_optional,
                           clock_groups_added, "Clock Groups")

        # Check sw_cg values are valid
        if group['sw_cg'] not in ['yes', 'no', 'hint']:
            log.error("Incorrect attribute for sw_cg: {}".format(
                group['sw_cg']))
            error += 1

        # Check combination of src and sw are valid
        if group['src'] == 'yes' and group['sw_cg'] != 'no':
            log.error("Invalid combination of src and sw_cg: {} and {}".format(
                group['src'], group['sw_cg']))
            error += 1

        # Check combination of sw_cg and unique are valid
        unique = group['unique'] if 'unique' in group else 'no'
        if group['sw_cg'] == 'no' and unique != 'no':
            log.error(
                "Incorrect attribute combination.  When sw_cg is no, unique must be no"
            )
            error += 1

        if error:
            break

    return error


def check_clocks_resets(top, ipobjs, ip_idxs, xbarobjs, xbar_idxs):

    error = 0

    # there should only be one each of pwrmgr/clkmgr/rstmgr
    pwrmgrs = [m for m in top['module'] if m['type'] == 'pwrmgr']
    clkmgrs = [m for m in top['module'] if m['type'] == 'clkmgr']
    rstmgrs = [m for m in top['module'] if m['type'] == 'rstmgr']

    if len(pwrmgrs) == 1 * len(clkmgrs) == 1 * len(rstmgrs) != 1:
        log.error("Incorrect number of pwrmgr/clkmgr/rstmgr")
        error += 1

    # check clock fields are all there
    ext_srcs = []
    for src in top['clocks']['srcs']:
        check_keys(src, clock_srcs_required, clock_srcs_optional, {},
                   "Clock source")
        ext_srcs.append(src['name'])

    # check derived clock sources
    log.info("Collected clocks are {}".format(ext_srcs))
    for src in top['clocks']['derived_srcs']:
        check_keys(src, derived_clock_srcs_required, {}, {}, "Derived clocks")
        try:
            ext_srcs.index(src['src'])
        except Exception:
            error += 1
            log.error("{} is not a valid src for {}".format(
                src['src'], src['name']))

    # all defined clock/reset nets
    reset_nets = [reset['name'] for reset in top['resets']['nodes']]
    clock_srcs = [
        clock['name']
        for clock in top['clocks']['srcs'] + top['clocks']['derived_srcs']
    ]

    # Check clock/reset port connection for all IPs
    for ipcfg in top['module']:
        ipcfg_name = ipcfg['name'].lower()
        log.info("Checking clock/resets for %s" % ipcfg_name)
        error += validate_reset(ipcfg, ipobjs[ip_idxs[ipcfg_name]], reset_nets)
        error += validate_clock(ipcfg, ipobjs[ip_idxs[ipcfg_name]], clock_srcs)

        if error:
            log.error("module clock/reset checking failed")
            break

    # Check clock/reset port connection for all xbars
    for xbarcfg in top['xbar']:
        xbarcfg_name = xbarcfg['name'].lower()
        log.info("Checking clock/resets for xbar %s" % xbarcfg_name)
        error += validate_reset(xbarcfg, xbarobjs[xbar_idxs[xbarcfg_name]],
                                reset_nets, "xbar")
        error += validate_clock(xbarcfg, xbarobjs[xbar_idxs[xbarcfg_name]],
                                clock_srcs, "xbar")

        if error:
            log.error("xbar clock/reset checking failed")
            break

    return error


# Checks the following
# For each defined reset connection in top*.hjson, there exists a defined port at the destination
# and defined reset net
# There are the same number of defined connections as there are ports
def validate_reset(top, inst, reset_nets, prefix=""):
    # Gather inst port list
    error = 0

    # Handle either an IpBlock (generated by reggen) or an OrderedDict
    # (generated by topgen for a crossbar)
    if isinstance(inst, IpBlock):
        name = inst.name
        reset_signals = inst.reset_signals
    else:
        name = inst['name']
        reset_signals = ([inst.get('reset_primary', 'rst_ni')] +
                         inst.get('other_reset_list', []))

    log.info("%s %s resets are %s" %
             (prefix, name, reset_signals))

    if len(top['reset_connections']) != len(reset_signals):
        error += 1
        log.error("%s %s mismatched number of reset ports and nets" %
                  (prefix, name))

    missing_port = [
        port for port in top['reset_connections'].keys()
        if port not in reset_signals
    ]

    if missing_port:
        error += 1
        log.error("%s %s Following reset ports do not exist:" %
                  (prefix, name))
        [log.error("%s" % port) for port in missing_port]

    missing_net = [
        net for port, net in top['reset_connections'].items()
        if net not in reset_nets
    ]

    if missing_net:
        error += 1
        log.error("%s %s Following reset nets do not exist:" %
                  (prefix, name))
        [log.error("%s" % net) for net in missing_net]

    return error


# Checks the following
# For each defined clock_src in top*.hjson, there exists a defined port at the destination
# and defined clock source
# There are the same number of defined connections as there are ports
def validate_clock(top, inst, clock_srcs, prefix=""):
    # Gather inst port list
    error = 0

    # Handle either an IpBlock (generated by reggen) or an OrderedDict
    # (generated by topgen for a crossbar)
    if isinstance(inst, IpBlock):
        name = inst.name
        clock_signals = inst.clock_signals
    else:
        name = inst['name']
        clock_signals = ([inst.get('clock_primary', 'rst_ni')] +
                         inst.get('other_clock_list', []))

    if len(top['clock_srcs']) != len(clock_signals):
        error += 1
        log.error("%s %s mismatched number of clock ports and nets" %
                  (prefix, name))

    missing_port = [
        port for port in top['clock_srcs'].keys()
        if port not in clock_signals
    ]

    if missing_port:
        error += 1
        log.error("%s %s Following clock ports do not exist:" %
                  (prefix, name))
        [log.error("%s" % port) for port in missing_port]

    missing_net = [
        net for port, net in top['clock_srcs'].items() if net not in clock_srcs
    ]

    if missing_net:
        error += 1
        log.error("%s %s Following clock nets do not exist:" %
                  (prefix, name))
        [log.error("%s" % net) for net in missing_net]

    return error


def check_flash(top):
    error = 0

    for mem in top['memory']:
        if mem['type'] == "eflash":
            error = check_keys(mem, eflash_required, eflash_optional,
                               eflash_added, "Eflash")

    flash = Flash(mem)
    error += 1 if not flash.check_values() else 0

    if error:
        log.error("Flash check failed")
    else:
        flash.populate(mem)

    return error


def check_power_domains(top):
    error = 0

    # check that the default domain is valid
    if top['power']['default'] not in top['power']['domains']:
        error += 1
        return error

    # check that power domain definition is consistent with reset and module definition
    for reset in top['resets']['nodes']:
        if reset['gen']:
            if 'domains' not in reset:
                log.error("{} missing domain definition".format(reset['name']))
                error += 1
                return error
            else:
                for domain in reset['domains']:
                    if domain not in top['power']['domains']:
                        log.error("{} defined invalid domain {}".format(
                            reset['name'], domain))
                        error += 1
                        return error

    # Check that each module, xbar, memory has a power domain defined.
    # If not, give it a default.
    # If there is one defined, check that it is a valid definition
    for end_point in top['module'] + top['memory'] + top['xbar']:
        if 'domain' not in end_point:
            end_point['domain'] = top['power']['default']

        if end_point['domain'] not in top['power']['domains']:
            log.error("{} defined invalid domain {}"
                      .format(end_point['name'],
                              end_point['domain']))
            error += 1
            return error

    # arrived without incident, return
    return error


def validate_top(top, ipobjs, xbarobjs):
    # return as it is for now
    error = check_keys(top, top_required, top_optional, top_added, "top")

    if error != 0:
        log.error("Top HJSON has top level errors. Aborting")
        return top, error

    component = top['name']

    # MODULE check
    err, ip_idxs = check_target(top, ipobjs, Target(TargetType.MODULE))
    error += err

    # XBAR check
    err, xbar_idxs = check_target(top, xbarobjs, Target(TargetType.XBAR))
    error += err

    # MEMORY check
    error += check_flash(top)

    # Power domain check
    error += check_power_domains(top)

    # Clock / Reset check
    error += check_clocks_resets(top, ipobjs, ip_idxs, xbarobjs, xbar_idxs)

    # Clock group check
    error += check_clock_groups(top)

    # RV_PLIC check

    # Pinout, pinmux and target checks
    # Note that these checks must happen in this order, as
    # the pinmux and target configs depend on the pinout.
    error += check_pinout(top, component)
    error += check_pinmux(top, component)
    error += check_implementation_targets(top, component)

    return top, error
