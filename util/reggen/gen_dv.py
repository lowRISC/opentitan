# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generate SystemVerilog designs from validated register json tree
"""

import logging as log
import operator
import sys

from mako.template import Template
from pkg_resources import resource_filename

from .field_enums import HwAccess, SwAccess, SwRdAccess, SwWrAccess
from .gen_rtl import Block, Field, Register, Window, json_to_reg


# function get block class name
def bcname(b):
    return b.name + "_reg_block"


# function get reg class name
def rcname(b, r):
    return b.name + "_reg_" + r.name


# function get mem class name
def mcname(b, m):
    return b.name + "_mem_" + m.name.lower()


# function get mem inst name
def miname(m):
    return m.name.lower()


# function get base addr in SV syntax
def sv_base_addr(b):
    sv_base_addr = b.base_addr.replace("0x", str(b.width) + "'h")
    return sv_base_addr


# function generate dv ral model using raw dict object parsed from hjson
def gen_dv(obj, outdir):
    # obj: OrderedDict
    block = json_to_reg(obj)
    gen_ral(block, outdir)


# function generate dv ral model using gen_rtl::Block specification
def gen_ral(block, outdir):
    # Read Register templates
    uvm_reg_tpl = Template(
        filename=resource_filename('reggen', 'uvm_reg.tpl.sv'))

    # Generate pkg.sv with block name
    with open(outdir + "/" + block.name + "_reg_block.sv", 'w') as fout:
        fout.write(
            uvm_reg_tpl.render(
                block=block,
                HwAccess=HwAccess,
                SwRdAccess=SwRdAccess,
                SwWrAccess=SwWrAccess))
