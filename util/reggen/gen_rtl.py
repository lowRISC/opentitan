# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generate SystemVerilog designs from validated register JSON tree
"""

import logging as log

from mako import exceptions
from mako.template import Template
from pkg_resources import resource_filename

from .access import HwAccess, SwRdAccess, SwWrAccess
from .data import Block


def escape_name(name):
    return name.lower().replace(' ', '_')


def check_field_bool(obj, field, default):
    if field in obj:
        return True if obj[field] == "true" else False
    else:
        return default


def json_to_reg(obj):
    """Converts JSON OrderedDict into structure having useful information for
    Template to use.

    Main purpose of this function is:
        - Add Offset value based on auto calculation
        - Prepare Systemverilog data structure to generate _pkg file
    """
    block = Block()

    # Name
    block.name = escape_name(obj["name"])
    log.info("Processing module: %s", block.name)

    block.width = int(obj["regwidth"], 0)

    if block.width != 32 and block.width != 64:
        log.error(
            "Current reggen tool doesn't support field width that is not 32 nor 64"
        )

    log.info("Data Width is set to %d bits", block.width)

    block.params = obj["param_list"] if "param_list" in obj else []

    block.hier_path = obj["hier_path"] if "hier_path" in obj else ""

    block.reg_block = obj['registers']

    # Last offset and calculate space
    #  Later on, it could use block.regs[-1].genoffset
    if "space" in obj:
        block.addr_width = int(obj["space"], 0).bit_length()
    else:
        block.addr_width = (obj["gensize"] - 1).bit_length()

    return block


def gen_rtl(obj, outdir):
    # obj: OrderedDict

    block = json_to_reg(obj)

    # Read Register templates
    reg_top_tpl = Template(
        filename=resource_filename('reggen', 'reg_top.sv.tpl'))
    reg_pkg_tpl = Template(
        filename=resource_filename('reggen', 'reg_pkg.sv.tpl'))

    # Generate pkg.sv with block name
    with open(outdir + "/" + block.name + "_reg_pkg.sv", 'w',
              encoding='UTF-8') as fout:
        try:
            fout.write(
                reg_pkg_tpl.render(block=block,
                                   HwAccess=HwAccess,
                                   SwRdAccess=SwRdAccess,
                                   SwWrAccess=SwWrAccess))
        except:  # noqa F722 for template Exception handling
            log.error(exceptions.text_error_template().render())
            return 1

    # Generate top.sv
    with open(outdir + "/" + block.name + "_reg_top.sv", 'w',
              encoding='UTF-8') as fout:
        try:
            fout.write(
                reg_top_tpl.render(block=block,
                                   HwAccess=HwAccess,
                                   SwRdAccess=SwRdAccess,
                                   SwWrAccess=SwWrAccess))
        except:  # noqa F722 for template Exception handling
            log.error(exceptions.text_error_template().render())
            return 1

    return 0
