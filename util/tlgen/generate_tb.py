# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
from pathlib import Path

from mako import exceptions
from mako.template import Template
from pkg_resources import resource_filename

from .xbar import Xbar


def generate_tb(xbar: Xbar,
                dv_path: Path,
                library_name: str = "ip") -> str:  # xbar: Xbar -> str
    # list all the generate files for TB
    tb_files = [
        "xbar_env_pkg__params.sv", "tb__xbar_connect.sv", "xbar.sim.core",
        "xbar.bind.core", "xbar.bind.sv", "xbar.sim_cfg.hjson",
        "xbar.testplan.hjson", "xbar_cov_excl.el", "xbar_cover.cfg"
    ]

    for fname in tb_files:
        tpl = Template(filename=resource_filename('tlgen', fname + '.tpl'))

        # some files need to be renamed
        if fname == "xbar.sim.core":
            fname = "xbar_%s_sim.core" % (xbar.name)
        elif fname == "xbar.bind.core":
            fname = "xbar_%s_bind.core" % (xbar.name)
        elif fname == "xbar.bind.sv":
            fname = "xbar_%s_bind.sv" % (xbar.name)
        elif fname == "xbar.sim_cfg.hjson":
            fname = "xbar_%s_sim_cfg.hjson" % (xbar.name)
        elif fname == "xbar.testplan.hjson":
            fname = "xbar_%s_testplan.hjson" % (xbar.name)

        # save testplan at data directory
        if fname == "xbar_%s_testplan.hjson" % (xbar.name):
            data_filepath = dv_path / '../../data/autogen'
            data_filepath.mkdir(parents=True, exist_ok=True)
            dv_filepath = data_filepath / fname
        else:
            dv_filepath = dv_path / fname

        with dv_filepath.open(mode='w', encoding='UTF-8') as fout:
            try:
                fout.write(tpl.render(xbar=xbar, library_name=library_name))
            except:  # noqa: E722 for general exception handling
                log.error(exceptions.text_error_template().render())
