# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log

from mako import exceptions
from mako.template import Template
from pkg_resources import resource_filename

from .item import NodeType
from .xbar import Xbar


def generate(xbar: Xbar, library_name: str = "ip") -> str:
    """generate uses elaborated model then creates top level Xbar module
    with prefix.
    """

    xbar_rtl_tpl = Template(
        filename=resource_filename('tlgen', 'xbar.rtl.sv.tpl'))
    xbar_pkg_tpl = Template(
        filename=resource_filename('tlgen', 'xbar.pkg.sv.tpl'))
    xbar_core_tpl = Template(
        filename=resource_filename('tlgen', 'xbar.core.tpl'))
    xbar_hjson_tpl = Template(
        filename=resource_filename('tlgen', 'xbar.hjson.tpl'))
    try:
        out_rtl = xbar_rtl_tpl.render(xbar=xbar, ntype=NodeType)
        out_pkg = xbar_pkg_tpl.render(xbar=xbar)
        out_core = xbar_core_tpl.render(xbar=xbar,
                                        ntype=NodeType,
                                        library_name=library_name)
        out_hjson = xbar_hjson_tpl.render(xbar=xbar)
    except:  # noqa: E722
        log.error(exceptions.text_error_template().render())

    results = []
    results.append(("rtl/autogen/xbar_%s.sv" % (xbar.name), out_rtl))
    results.append(("rtl/autogen/tl_%s_pkg.sv" % (xbar.name), out_pkg))
    results.append(("xbar_%s.core" % (xbar.name), out_core))
    results.append(("data/autogen/xbar_%s.hjson" % (xbar.name), out_hjson))

    return results
