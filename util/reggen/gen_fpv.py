# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
# # Lint as: python3
#
"""Generate FPV CSR read and write assertions from validated register JSON tree
"""

import logging as log
import operator
import sys

from mako import exceptions
from mako.template import Template
from pkg_resources import resource_filename

from .data import *
from .field_enums import HwAccess, SwAccess, SwRdAccess, SwWrAccess
from .gen_rtl import json_to_reg


# function get write property name
def wpname(r):
    return r.name + "_wr_p"


# function get read property name
def rpname(r):
    return r.name + "_rd_p"


def gen_fpv(obj, outdir):
    # obj: OrderedDict
    block = json_to_reg(obj)
    gen_assertion(block, outdir)


def gen_assertion(block, outdir):
    # Read Register templates
    fpv_csr_tpl = Template(
        filename=resource_filename('reggen', 'fpv_csr.sv.tpl'))

    # Generate pkg.sv with block name
    with open(outdir + "/" + block.name + "_csr_assert_fpv.sv", 'w') as fout:
        try:
            fout.write(
                fpv_csr_tpl.render(block=block,
                                   HwAccess=HwAccess,
                                   SwRdAccess=SwRdAccess,
                                   SwWrAccess=SwWrAccess))
        except:
            log.error(exceptions.text_error_template().render())
