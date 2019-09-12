# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from mako.template import Template
from pkg_resources import resource_filename

from .item import NodeType
from .xbar import Xbar


def generate(xbar):  #xbar: Xbar -> str
    """generate uses elaborated model then creates top level Xbar module
    with prefix.
    """

    xbar_rtl_tpl = Template(
        filename=resource_filename('tlgen', 'xbar.rtl.tpl.sv'))
    xbar_pkg_tpl = Template(
        filename=resource_filename('tlgen', 'xbar.pkg.tpl.sv'))
    #xbar_dv_tpl = Template(
    #    filename=resource_filename('tlgen', 'xbar.dv.tpl.sv'))
    xbar_bind_tpl = Template(
        filename=resource_filename('tlgen', 'xbar.bind.tpl.sv'))

    out_rtl = xbar_rtl_tpl.render(xbar=xbar, ntype=NodeType)
    out_pkg = xbar_pkg_tpl.render(xbar=xbar)
    out_bind = xbar_bind_tpl.render(xbar=xbar, ntype=NodeType)
    return (out_rtl, out_pkg, out_bind)
