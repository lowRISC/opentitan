# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
# # Lint as: python3
#
"""Generate FPV CSR read and write assertions from validated register JSON tree
"""

import logging as log
import os.path

import yaml
from mako import exceptions
from mako.template import Template
from pkg_resources import resource_filename

from .access import HwAccess, SwRdAccess, SwWrAccess
from .ip_block import IpBlock


# function get write property name
def wpname(r):
    return r.name + "_wr_p"


# function get read property name
def rpname(r):
    return r.name + "_rd_p"


def gen_fpv(block: IpBlock, outdir):
    # Read Register templates
    fpv_csr_tpl = Template(
        filename=resource_filename('reggen', 'fpv_csr.sv.tpl'))

    # Generate pkg.sv with block name
    lblock = block.name.lower()
    mod_name = lblock + '_csr_assert_fpv'
    file_name = mod_name + '.sv'
    with open(os.path.join(outdir, file_name), 'w') as fout:
        try:
            fout.write(
                fpv_csr_tpl.render(block=block,
                                   HwAccess=HwAccess,
                                   SwRdAccess=SwRdAccess,
                                   SwWrAccess=SwWrAccess))
        except:  # noqa: 722
            log.error(exceptions.text_error_template().render())
            return 1

    # Generate a fusesoc core file that points at the files we've just
    # generated.
    core_data = {
        'name': "lowrisc:fpv:{}_csr_assert".format(lblock),
        'filesets': {
            'files_dv': {
                'depend': [
                    "lowrisc:ip:{}".format(lblock),
                    "lowrisc:tlul:headers",
                    "lowrisc:prim:assert",
                ],
                'files': [file_name],
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
