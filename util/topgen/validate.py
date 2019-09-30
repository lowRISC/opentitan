# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log

from reggen.validate import val_types, check_keys
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
#     'pi': ["python int", "Native python type int (generated)"],
#     'pb': ["python Bool", "Native python type Bool (generated)"],
#     'pl': ["python list", "Native python type list (generated)"],
#     'pe': ["python enum", "Native python type enum (generated)"]
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
    'pinmux': ['g', 'pinmux definition if doesn\'t exist, tool uses defaults'],
    'padctrl':
    ['g', 'PADS instantiation, if doesn\'t exist, tool creates direct output'],
}

top_added = {}

pinmux_required = {}
pinmux_optional = {
    'dio_modules': ['l', 'List of Dedicated IO.'],
    'mio_modules': ['l', 'List of Multiplexing IO'],
    'nc_modules': ['l', 'List of NotConnected IO'],
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


def check_padctrl(top, prefix):
    error = check_keys(top["padctrl"], padctrl_required, padctrl_optional,
                       padctrl_added, prefix + " PadControl")
    return error


def check_pinmux(top, prefix):
    return 0


def validate_top(top):
    # return as it is for now
    error = check_keys(top, top_required, top_optional, top_added, "top")

    if error != 0:
        log.error("Top HJSON has top level errors. Aborting")
        return top, error

    component = top['name']

    ## MODULE check

    ## MEMORY check

    ## RV_PLIC check

    ## PINMUX & PADS check
    if not "padctrl" in top:
        log.warning("padsctrl field doesn't exist in top. Skipping pads \
                     generation. Top input/output are directly connected from \
                     peripherals.")
    # Pads configuration check
    else:
        error = check_padctrl(top, component)

    if not "pinmux" in top:
        log.warning("Top {} has no 'pinmux' field. Please consider specifying \
                        pinmux and pads configuration")
        top["pinmux"] = {}
    # checking pinmux after pads as dio connects to PAD

    error += check_pinmux(top, component)

    ## XBAR check

    return top, error
