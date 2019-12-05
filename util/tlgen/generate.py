# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
from mako import exceptions
from mako.template import Template
from pkg_resources import resource_filename

from .item import NodeType
from .xbar import Xbar



def generate(xbar):  #xbar: Xbar -> str
    """generate uses elaborated model then creates top level Xbar module
    with prefix.
    """

    xbar_rtl_tpl = Template(
        filename=resource_filename('tlgen', 'xbar.rtl.sv.tpl'))
    xbar_pkg_tpl = Template(
        filename=resource_filename('tlgen', 'xbar.pkg.sv.tpl'))
    #xbar_dv_tpl = Template(
    #    filename=resource_filename('tlgen', 'xbar.dv.sv.tpl'))
    xbar_core_tpl = Template(
        filename=resource_filename('tlgen', 'xbar.core.tpl'))

    try:
        out_rtl = xbar_rtl_tpl.render(xbar=xbar, ntype=NodeType)
        out_pkg = xbar_pkg_tpl.render(xbar=xbar)
        out_core = xbar_core_tpl.render(xbar=xbar, ntype=NodeType)
    except:
        log.error(exceptions.text_error_template().render())

    return (out_rtl, out_pkg, out_core)
