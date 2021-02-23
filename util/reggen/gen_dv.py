# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
'''Generate DV code for an IP block'''

import logging as log

from mako import exceptions
from mako.template import Template
from pkg_resources import resource_filename

from .access import HwAccess, SwRdAccess, SwWrAccess
from .block import Block
from .top import Top
from .ip_block import IpBlock


def bcname(b):
    '''Get the name of the dv_base_reg_block subclass for this block'''
    return b.name.lower() + "_reg_block"


def rcname(b, r):
    '''Get the name of the dv_base_reg subclass for this register'''
    return b.name.lower() + "_reg_" + r.name.lower()


def mcname(b, m):
    '''Get the name of the dv_base_mem subclass for this memory'''
    return b.name.lower() + "_mem_" + m.name.lower()


def miname(m):
    '''Get the lower-case name of a memory block'''
    return m.name.lower()


def sv_base_addr(top: Top, inst_name: str):
    '''Get the base address of a block in SV syntax'''
    return "{}'h{:x}".format(top.regwidth,
                             top.by_inst_name[inst_name][0])


def gen_dv(block: IpBlock, dv_base_prefix, outdir):
    '''Generate DV files for an IpBlock'''
    gen_ral(block, dv_base_prefix, outdir)


def gen_ral(block: Block, dv_base_prefix, outdir):
    '''Generate DV RAL model for a Block'''
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
        return 1

    # Dump to output file
    dest_path = '{}/{}_ral_pkg.sv'.format(outdir, block.name.lower())
    with open(dest_path, 'w') as fout:
        fout.write(to_write)

    return 0
