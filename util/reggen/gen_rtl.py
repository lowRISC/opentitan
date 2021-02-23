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
from .ip_block import IpBlock


def escape_name(name):
    return name.lower().replace(' ', '_')


def gen_rtl(block: IpBlock, outdir: str):
    # Read Register templates
    reg_top_tpl = Template(
        filename=resource_filename('reggen', 'reg_top.sv.tpl'))
    reg_pkg_tpl = Template(
        filename=resource_filename('reggen', 'reg_pkg.sv.tpl'))

    # Generate pkg.sv with block name
    with open(outdir + "/" + block.name.lower() + "_reg_pkg.sv", 'w',
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
    with open(outdir + "/" + block.name.lower() + "_reg_top.sv", 'w',
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
