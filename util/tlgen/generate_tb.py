# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log

from mako import exceptions
from mako.template import Template
from pkg_resources import resource_filename

from .item import NodeType
from .xbar import Xbar


def generate_tb(xbar, dv_path):  #xbar: Xbar -> str
    # list all the generate files for TB
    tb_files = [
        "xbar_env_pkg__params.sv", "tb__xbar_connect.sv", "xbar.sim.core",
        "xbar.bind.sv", "Makefile"
    ]

    for fname in tb_files:
        tpl = Template(filename=resource_filename('tlgen', fname + '.tpl'))

        # some files need to be renamed
        if fname == "xbar.sim.core":
            fname = "xbar_%s_sim.core" % (xbar.name)
        elif fname == "xbar.bind.sv":
            fname = "xbar_%s_bind.sv" % (xbar.name)

        dv_filepath = dv_path / fname
        with dv_filepath.open(mode='w', encoding='UTF-8') as fout:
            try:
                fout.write(tpl.render(xbar=xbar))
            except:
                log.error(exceptions.text_error_template().render())
