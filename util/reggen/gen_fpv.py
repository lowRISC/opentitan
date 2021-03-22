# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
# # Lint as: python3
#
"""Generate FPV CSR read and write assertions from IpBlock
"""

import logging as log
import os.path

import yaml
from mako import exceptions
from mako.template import Template
from pkg_resources import resource_filename

from .ip_block import IpBlock


def gen_fpv(block: IpBlock, outdir):
    # Read Register templates
    fpv_csr_tpl = Template(
        filename=resource_filename('reggen', 'fpv_csr.sv.tpl'))

    # Generate a module with CSR assertions for each device interface. For a
    # device interface with no name, we generate <block>_csr_assert_fpv. For a
    # named interface, we generate <block>_<ifname>_csr_assert_fpv.
    lblock = block.name.lower()
    generated = []
    for if_name, rb in block.reg_blocks.items():
        if not rb.flat_regs:
            # No registers to check!
            continue

        if if_name is None:
            mod_base = lblock
        else:
            mod_base = lblock + '_' + if_name.lower()

        mod_name = mod_base + '_csr_assert_fpv'
        filename = mod_name + '.sv'
        generated.append(filename)
        reg_top_path = os.path.join(outdir, filename)
        with open(reg_top_path, 'w', encoding='UTF-8') as fout:
            try:
                fout.write(fpv_csr_tpl.render(block=block,
                                              mod_base=mod_base,
                                              if_name=if_name,
                                              rb=rb))
            except:  # noqa F722 for template Exception handling
                log.error(exceptions.text_error_template().render())
                return 1

    # Generate a fusesoc core file that points at the files we've just
    # generated.
    core_data = {
        'name': "lowrisc:fpv:{}_csr_assert".format(lblock),
        'filesets': {
            'files_dv': {
                'depend': [
                    "lowrisc:tlul:headers",
                    "lowrisc:prim:assert",
                ],
                'files': generated,
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
    core_file_path = os.path.join(outdir, lblock + '_csr_assert_fpv.core')
    with open(core_file_path, 'w') as core_file:
        core_file.write('CAPI=2:\n')
        yaml.dump(core_data, core_file, encoding='utf-8')

    return 0
