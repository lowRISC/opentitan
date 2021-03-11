# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
'''Generate DV code for an IP block'''

import logging as log
import os
from typing import List, Optional, Tuple

import yaml

from mako import exceptions  # type: ignore
from mako.lookup import TemplateLookup  # type: ignore
from pkg_resources import resource_filename

from .ip_block import IpBlock
from .register import Register
from .top import Top
from .window import Window


def bcname(esc_if_name: str) -> str:
    '''Get the name of the dv_base_reg_block subclass for this device interface'''
    return esc_if_name + "_reg_block"


def rcname(esc_if_name: str, r: Register) -> str:
    '''Get the name of the dv_base_reg subclass for this register'''
    return '{}_reg_{}'.format(esc_if_name, r.name.lower())


def mcname(esc_if_name: str, m: Window) -> str:
    '''Get the name of the dv_base_mem subclass for this memory'''
    return '{}_mem_{}'.format(esc_if_name, m.name.lower())


def miname(m: Window) -> str:
    '''Get the lower-case name of a memory block'''
    return m.name.lower()


def sv_base_addr(top: Top, if_name: Tuple[str, Optional[str]]) -> str:
    '''Get the base address of a device interface in SV syntax'''
    return "{}'h{:x}".format(top.regwidth, top.if_addrs[if_name])


def _gen_core_file(outdir: str,
                   lblock: str,
                   dv_base_prefix: str,
                   paths: List[str]) -> None:
    depends = ["lowrisc:dv:dv_base_reg"]
    if dv_base_prefix and dv_base_prefix != "dv_base":
        depends.append("lowrisc:dv:{}_reg".format(dv_base_prefix))

    # Generate a fusesoc core file that points at the files we've just
    # generated.
    core_data = {
        'name': "lowrisc:dv:{}_ral_pkg".format(lblock),
        'filesets': {
            'files_dv': {
                'depend': depends,
                'files': paths,
                'file_type': 'systemVerilogSource'
            },
        },
        'targets': {
            'default': {
                'filesets': [
                    'files_dv',
                ],
            },
        },
    }
    core_file_path = os.path.join(outdir, lblock + '_ral_pkg.core')
    with open(core_file_path, 'w') as core_file:
        core_file.write('CAPI=2:\n')
        yaml.dump(core_data, core_file, encoding='utf-8')


def gen_dv(block: IpBlock, dv_base_prefix: str, outdir: str) -> int:
    '''Generate DV files for an IpBlock'''

    lookup = TemplateLookup(directories=[resource_filename('reggen', '.')])
    uvm_reg_tpl = lookup.get_template('uvm_reg.sv.tpl')

    # Generate the RAL package(s). For a device interface with no name we
    # generate the package "<block>_ral_pkg" (writing to <block>_ral_pkg.sv).
    # In any other case, we also need the interface name, giving
    # <block>_<ifname>_ral_pkg.
    generated = []

    lblock = block.name.lower()
    for if_name, rb in block.reg_blocks.items():
        if if_name is None:
            mod_base = lblock
        else:
            mod_base = lblock + '_' + if_name.lower()

        file_name = mod_base + '_ral_pkg.sv'
        generated.append(file_name)
        reg_top_path = os.path.join(outdir, file_name)
        with open(reg_top_path, 'w', encoding='UTF-8') as fout:
            try:
                fout.write(uvm_reg_tpl.render(rb=rb,
                                              block=block,
                                              esc_if_name=mod_base,
                                              dv_base_prefix=dv_base_prefix))
            except:  # noqa F722 for template Exception handling
                log.error(exceptions.text_error_template().render())
                return 1

    _gen_core_file(outdir, lblock, dv_base_prefix, generated)
    return 0


def gen_top_dv(top: Top,
               dv_base_prefix: str,
               outdir: str) -> int:
    '''Generate DV RAL model for a Top'''
    # Read template
    lookup = TemplateLookup(directories=[resource_filename('reggen', '.')])
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

    _gen_core_file(outdir, 'chip', dv_base_prefix, ['chip_ral_pkg.sv'])

    return 0
