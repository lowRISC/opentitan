# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
from typing import Optional, Tuple

from mako import exceptions  # type: ignore
from mako.lookup import TemplateLookup  # type: ignore
from pkg_resources import resource_filename

from reggen.gen_dv import gen_core_file

from .top import Top


def sv_base_addr(top: Top, if_name: Tuple[str, Optional[str]]) -> str:
    '''Get the base address of a device interface in SV syntax'''
    return "{}'h{:x}".format(top.regwidth, top.if_addrs[if_name])


def gen_dv(top: Top,
           dv_base_prefix: str,
           outdir: str) -> int:
    '''Generate DV RAL model for a Top'''
    # Read template
    lookup = TemplateLookup(directories=[resource_filename('topgen', '.'),
                                         resource_filename('reggen', '.')])
    uvm_reg_tpl = lookup.get_template('top_uvm_reg.sv.tpl')

    # Expand template
    try:
        to_write = uvm_reg_tpl.render(top=top,
                                      dv_base_prefix=dv_base_prefix)
    except:  # noqa: E722
        log.error(exceptions.text_error_template().render())
        return 1

    # Dump to output file
    dest_path = '{}/chip_ral_pkg.sv'.format(outdir)
    with open(dest_path, 'w') as fout:
        fout.write(to_write)

    gen_core_file(outdir, 'chip', dv_base_prefix, ['chip_ral_pkg.sv'])

    return 0
