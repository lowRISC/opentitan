# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
import logging as log
from enum import Enum

from reggen.validate import check_keys, val_types

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
    'clocks': ['l', 'list of clocks'],
    'module': ['l', 'list of modules to instantiate'],
    'memory': [
        'l', 'list of memories. At least one memory is needed to run \
               the software'
    ],
    'debug_mem_base_addr':
    ['d', 'Base address of RV_DM. Planned to move to \
module'],
    'xbar': ['l', 'List of the xbar used in the top'],
}

top_optional = {
    'interrupt_modules': ['l', 'list of the modules that connects to rv_plic'],
    'interrupt': ['lnw', 'interrupts (generated)'],
    'alert_modules': ['l', 'list of the modules that connects to alert_handler'],
    'alert': ['lnw', 'alerts (generated)'],
    'alert_async': ['l', 'async alerts (generated)'],
    'pinmux': ['g', 'pinmux definition if doesn\'t exist, tool uses defaults'],
    'padctrl':
    ['g', 'PADS instantiation, if doesn\'t exist, tool creates direct output'],
}

top_added = {}

pinmux_required = {}
pinmux_optional = {
    'num_mio': ['d', 'Number of Multiplexed IOs'\
                ' If padctrl is used, this value will be replaced with #pads'\
                ' - #DIO'],
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


class TargetType(Enum):
    MODULE = "module"
    XBAR = "xbar"


class Target:
    """Target class informs the checkers if we are validating a module or xbar
    """

    # The type of this target
    target_type = ""

    # The key to search against
    key = ""

    def __init__(self, target_type):
        self.target_type = target_type
        if target_type == TargetType.MODULE:
            self.key = "type"
        else:
            self.key = "name"


# Check to see if each module/xbar defined in top.hjson exists as ip/xbar.hjson
# Also check to make sure there are not multiple definitions of ip/xbar.hjson for each
# top level definition
# If it does, return a dictionary of instance names to index in ip/xbarobjs
def check_target(top, objs, tgtobj):
    error = 0
    idxs = {}

    for i in range(len(objs)):
        log.info("%d Order is %s" % (i, objs[i]['name'].lower()))

    tgt_type = tgtobj.target_type.value
    inst_key = tgtobj.key

    for cfg in top[tgt_type]:
        cfg_name = cfg['name'].lower()
        log.info("Checking target %s %s" % (tgt_type, cfg_name))
        tgt_def = [o for o in objs if cfg[inst_key] == o['name'].lower()]
        error += check_def(tgt_def, cfg_name)
        if error:
            log.error("Target existence check failed")
            break
        else:
            idxs[cfg_name] = objs.index(tgt_def[0])

    log.info("Current state %s" % idxs)
    return error, idxs


def check_padctrl(top, prefix):
    error = check_keys(top["padctrl"], padctrl_required, padctrl_optional,
                       padctrl_added, prefix + " PadControl")
    return error


def check_pinmux(top, prefix):
    return 0


def check_clocks_resets(top, ipobjs, ip_idxs, xbarobjs, xbar_idxs):
    # all defined clock/reset nets
    reset_nets = [reset['name'] for reset in top['resets']]
    clock_nets = [clock['name'] for clock in top['clocks']]
    error = 0

    # Check clock/reset port connection for all IPs
    for ipcfg in top['module']:
        ipcfg_name = ipcfg['name'].lower()
        log.info("Checking clock/resets for %s" % ipcfg_name)
        error += validate_reset(ipcfg, ipobjs[ip_idxs[ipcfg_name]], reset_nets)
        error += validate_clock(ipcfg, ipobjs[ip_idxs[ipcfg_name]], clock_nets)

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
                                clock_nets, "xbar")

        if error:
            log.error("xbar clock/reset checking failed")
            break

    return error


def check_def(inst_def, name):
    error = 0
    if not inst_def:
        log.error("Could not find %s.hjson" % name)
        error += 1

    if len(inst_def) > 1:
        log.error("Duplicate %s.hjson" % name)
        error += 1

    return error


# Checks the following
# For each defined reset connection in top*.hjson, there exists a defined port at the destination
# and defined reset net
# There are the same number of defined connections as there are ports
def validate_reset(top, inst, reset_nets, prefix=""):
    # Gather inst port list
    error = 0
    inst_port_list = []
    if 'reset_primary' not in inst.keys():
        log.info("%s %s does not have a reset_primary defined, default used" %
                 (prefix, inst['name']))
        inst_port_list.append("rst_ni")
    else:
        inst_port_list.append(inst['reset_primary'])

    if 'other_reset_list' in inst.keys():
        inst_port_list.extend(inst['other_reset_list'])
    log.info("%s %s resets are %s" %
             (prefix, inst['name'].lower(), inst_port_list))

    if len(top['reset_connections'].keys()) != len(inst_port_list):
        error += 1
        log.error("%s %s mismatched number of reset ports and nets" %
                  (prefix, inst['name']))

    missing_port = [
        port for port in top['reset_connections'].keys()
        if port not in inst_port_list
    ]

    if missing_port:
        error += 1
        log.error("%s %s Following reset ports do not exist:" %
                  (prefix, inst['name']))
        [log.error("%s" % port) for port in missing_port]

    missing_net = [
        net for port, net in top['reset_connections'].items()
        if net not in reset_nets
    ]

    if missing_net:
        error += 1
        log.error("%s %s Following reset nets do not exist:" %
                  (prefix, inst['name']))
        [log.error("%s" % net) for net in missing_net]

    return error


# Checks the following
# For each defined clock connection in top*.hjson, there exists a defined port at the destination
# and defined clock net
# There are the same number of defined connections as there are ports
def validate_clock(top, inst, clock_nets, prefix=""):
    # Gather inst port list
    error = 0
    inst_port_list = []
    if 'clock_primary' not in inst.keys():
        log.info("%s %s does not have a clock_primary defined, default used" %
                 (prefix, inst['name']))
        inst_port_list.append("clk_i")
    else:
        inst_port_list.append(inst['clock_primary'])

    if 'other_clock_list' in inst.keys():
        inst_port_list.extend(inst['other_clock_list'])
    log.info("%s %s clocks are %s" %
             (prefix, inst['name'].lower(), inst_port_list))

    if len(top['clock_connections'].keys()) != len(inst_port_list):
        error += 1
        log.error("%s %s mismatched number of clock ports and nets" %
                  (prefix, inst['name']))

    missing_port = [
        port for port in top['clock_connections'].keys()
        if port not in inst_port_list
    ]

    if missing_port:
        error += 1
        log.error("%s %s Following clock ports do not exist:" %
                  (prefix, inst['name']))
        [log.error("%s" % port) for port in missing_port]

    missing_net = [
        net for port, net in top['clock_connections'].items()
        if net not in clock_nets
    ]

    if missing_net:
        error += 1
        log.error("%s %s Following clock nets do not exist:" %
                  (prefix, inst['name']))
        [log.error("%s" % net) for net in missing_net]

    return error


def validate_top(top, ipobjs, xbarobjs):
    # return as it is for now
    error = check_keys(top, top_required, top_optional, top_added, "top")

    if error != 0:
        log.error("Top HJSON has top level errors. Aborting")
        return top, error

    component = top['name']

    ## MODULE check
    err, ip_idxs = check_target(top, ipobjs, Target(TargetType.MODULE))
    error += err

    ## XBAR check
    err, xbar_idxs = check_target(top, xbarobjs, Target(TargetType.XBAR))
    error += err

    ## MEMORY check

    ## Clock / Reset check
    error += check_clocks_resets(top, ipobjs, ip_idxs, xbarobjs, xbar_idxs)

    ## RV_PLIC check

    ## PINMUX & PADS check
    if not "padctrl" in top:
        log.warning("padsctrl field doesn't exist in top. Skipping pads \
                     generation. Top input/output are directly connected from \
                     peripherals.")
    # Pads configuration check
    else:
        error += check_padctrl(top, component)

    if not "pinmux" in top:
        log.warning("Top {} has no 'pinmux' field. Please consider specifying \
                        pinmux and pads configuration")
        top["pinmux"] = {}
    # checking pinmux after pads as dio connects to PAD

    error += check_pinmux(top, component)

    return top, error
