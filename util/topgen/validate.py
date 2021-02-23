# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
import logging as log
from collections import OrderedDict
from enum import Enum

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
    'memory': [
        'l', 'list of memories. At least one memory is needed to run \
               the software'
    ],
    'debug_mem_base_addr':
    ['d', 'Base address of RV_DM. Planned to move to \
module'],
    'xbar': ['l', 'List of the xbar used in the top'],
    'rnd_cnst_seed': ['int', "Seed for random netlist constant computation"],
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
    'padctrl': [
        'g',
        'PADS instantiation, if doesn\'t exist, tool creates direct output'
    ],
    'pinmux': ['g', 'pinmux definition if doesn\'t exist, tool uses defaults'],
    'power': ['g', 'power domains supported by the design'],
    'port': ['g', 'assign special attributes to specific ports']
}

top_added = {}

pinmux_required = {}
pinmux_optional = {
    'num_mio': [
        'd', 'Number of Multiplexed IOs'
        ' If padctrl is used, this value will be replaced with #pads'
        ' - #DIO'
    ],
    'dio_modules': ['l', 'List of Dedicated IOs.'],
    'mio_modules': ['l', 'List of Multiplexed IPs/IOs'],
    'nc_modules': ['l', 'List of NotConnected IOs'],
}
pinmux_added = {
    'inputs': ['l', 'Full list of SoC inputs, `module_name.sig_name`'],
    'outputs': ['l', 'Full list of SoC outputs, `module_name.sig_name`'],
}

padctrl_required = {}
padctrl_optional = {
    'pads': ['l', 'List of pads'],
    'attr_default': ['l', 'List of the attribute']
}
padctrl_added = {}

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
        pow2_check = self.is_pow2(self.banks) and self.is_pow2(self.pages_per_bank) and \
        self.is_pow2(self.program_resolution)
        limit_check = (self.banks <= Flash.max_banks) \
            and (self.pages_per_bank <= Flash.max_pages_per_bank)

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


def check_padctrl(top, prefix):
    error = check_keys(top["padctrl"], padctrl_required, padctrl_optional,
                       padctrl_added, prefix + " PadControl")
    return error


def check_pinmux(top, prefix):
    return 0


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

    # PINMUX & PADS check
    if "padctrl" not in top:
        log.warning("padsctrl field doesn't exist in top. Skipping pads \
                     generation. Top input/output are directly connected from \
                     peripherals.")
    # Pads configuration check
    else:
        error += check_padctrl(top, component)

    if "pinmux" not in top:
        log.warning("Top {} has no 'pinmux' field. Please consider specifying \
                        pinmux and pads configuration")
        top["pinmux"] = OrderedDict()
    # checking pinmux after pads as dio connects to PAD

    error += check_pinmux(top, component)

    return top, error
