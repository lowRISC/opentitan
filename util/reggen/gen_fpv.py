# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
# # Lint as: python3
#
"""Generate FPV CSR read and write assertions from IpBlock
"""

import logging as log
import os.path

import yaml
from mako import exceptions  # type: ignore
from mako.template import Template  # type: ignore
import importlib_resources

from reggen.ip_block import IpBlock


def gen_fpv(block: IpBlock, outdir: str) -> int:
    # Read Register templates
    fpv_csr_tpl = Template(
        filename=str(importlib_resources.files('reggen') / "fpv_csr.sv.tpl"))

    device_hier_paths = block.bus_interfaces.device_hier_paths

    # Generate a module with CSR assertions for each device interface. For a
    # device interface with no name, we generate <block>_csr_assert_fpv. For a
    # named interface, we generate <block>_<ifname>_csr_assert_fpv.
    lblock = block.name.lower()
    generated = []
    for if_name, rb in block.reg_blocks.items():
        if not rb.flat_regs:
            # No registers to check!
            continue

        hier_path = device_hier_paths[if_name]
        if_suffix = '' if if_name is None else '_' + if_name.lower()
        reg_block_path = hier_path + if_suffix

        mod_base = lblock + if_suffix
        mod_name = mod_base + '_csr_assert_fpv'
        filename = mod_name + '.sv'
        generated.append(filename)
        reg_top_path = os.path.join(outdir, filename)
        with open(reg_top_path, 'w', encoding='UTF-8') as fout:
            try:
                fout.write(fpv_csr_tpl.render(block=block,
                                              reg_block_path=reg_block_path,
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
