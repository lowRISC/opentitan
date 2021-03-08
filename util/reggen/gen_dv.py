# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
'''Generate DV code for an IP block'''

import logging as log
from typing import Optional, Tuple, Union

from mako import exceptions  # type: ignore
from mako.template import Template  # type: ignore
from pkg_resources import resource_filename

from .access import HwAccess, SwRdAccess, SwWrAccess
from .ip_block import IpBlock
from .register import Register
from .top import Top
from .window import Window


def bcname(b: Union[IpBlock, Top]) -> str:
    '''Get the name of the dv_base_reg_block subclass for this block'''
    return b.name.lower() + "_reg_block"


def rcname(b: Union[IpBlock, Top], r: Register) -> str:
    '''Get the name of the dv_base_reg subclass for this register'''
    return b.name.lower() + "_reg_" + r.name.lower()


def mcname(b: Union[IpBlock, Top], m: Window) -> str:
    '''Get the name of the dv_base_mem subclass for this memory'''
    return b.name.lower() + "_mem_" + m.name.lower()


def miname(m: Window) -> str:
    '''Get the lower-case name of a memory block'''
    return m.name.lower()


def sv_base_addr(top: Top, if_name: Tuple[str, Optional[str]]) -> str:
    '''Get the base address of a device interface in SV syntax'''
    return "{}'h{:x}".format(top.regwidth, top.if_addrs[if_name])


def gen_dv(block: IpBlock, dv_base_prefix: str, outdir: str) -> int:
    '''Generate DV files for an IpBlock'''
    return gen_ral(block, dv_base_prefix, outdir)


def gen_ral(block: Union[IpBlock, Top],
            dv_base_prefix: str,
            outdir: str) -> int:
    '''Generate DV RAL model for an IpBlock or Top'''
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
