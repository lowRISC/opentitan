# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
'''Generate DV code for an IP block'''

import logging as log
import sys

from mako import exceptions
from mako.template import Template
from pkg_resources import resource_filename

from .field_enums import HwAccess, SwRdAccess, SwWrAccess
from .gen_rtl import json_to_reg


def bcname(b):
    '''Get the name of the dv_base_reg_block subclass for this block'''
    return b.name + "_reg_block"


def rcname(b, r):
    '''Get the name of the dv_base_reg subclass for this register'''
    return b.name + "_reg_" + r.name


def mcname(b, m):
    '''Get the name of the dv_base_mem subclass for this memory'''
    return b.name + "_mem_" + m.name.lower()


def miname(m):
    '''Get the lower-case name of a memory block'''
    return m.name.lower()


def sv_base_addr(b, inst):
    '''Get the base address of a block in SV syntax'''
    return "{}'h{:x}".format(b.width, b.base_addr[inst])


def gen_dv(obj, dv_base_prefix, outdir):
    '''Generate DV files using a raw dict object parsed from hjson'''
    gen_ral(json_to_reg(obj), dv_base_prefix, outdir)


def gen_ral(block, dv_base_prefix, outdir):
    '''Generate DV RAL model from a gen_rtl.Block specification'''

    # Read template
    tpl_filename = resource_filename('reggen', 'uvm_reg.sv.tpl')
    uvm_reg_tpl = Template(filename=tpl_filename)

    # Expand template
    try:
        to_write = uvm_reg_tpl.render(block=block,
                                      dv_base_prefix=dv_base_prefix,
                                      HwAccess=HwAccess,
                                      SwRdAccess=SwRdAccess,
                                      SwWrAccess=SwWrAccess)
    except:  # noqa: E722
        log.error(exceptions.text_error_template().render())
        sys.exit(1)

    # Dump to output file
    dest_path = '{}/{}_ral_pkg.sv'.format(outdir, block.name)
    with open(dest_path, 'w') as fout:
        fout.write(to_write)
