#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Clock Manager Generator
"""

import argparse
import logging as log
import sys
import subprocess
from collections import OrderedDict
from io import StringIO
from pathlib import Path

import hjson
from mako import exceptions
from mako.template import Template

# Common header for generated files
def main():

    current = Path(__file__).parent.absolute()

    hjson_tpl = Template(filename=str(current / '../data/clkmgr.hjson.tpl'))
    rtl_tpl   = Template(filename=str(current / '../data/clkmgr.sv.tpl'))
    pkg_tpl   = Template(filename=str(current / '../data/clkmgr_pkg.sv.tpl'))

    hjson_out = current / '../data/clkmgr.hjson'
    rtl_out   = current / '../rtl/clkmgr.sv'
    pkg_out   = current / '../rtl/clkmgr_pkg.sv'

    cfgpath   = current / '../data/clkmgr.cfg.example.hjson'

    try:
        with open(cfgpath, 'r') as cfg:
            topcfg = hjson.load(cfg,use_decimal=True,object_pairs_hook=OrderedDict)
    except ValueError:
        log.error("{} not found".format(cfgpath))
        raise SystemExit(sys.exc_info()[1])

    clks_attr = topcfg['clocks']
    grps = clks_attr['groups']

    # feedthrough clocks
    ft_clks = OrderedDict()
    rg_clks = OrderedDict()
    sw_clks = OrderedDict()
    hint_clks = OrderedDict()

    ft_clks   = {clk:src for grp in grps for (clk,src) in grp['clocks'].items()
                 if grp['name'] == 'powerup'}

    # root-gate clocks
    rg_clks   = {clk:src for grp in grps for (clk,src) in grp['clocks'].items()
                 if grp['name'] != 'powerup' and grp['sw_cg'] == 'no'}

    # direct sw control clocks
    sw_clks   = {clk:src for grp in grps for (clk,src) in grp['clocks'].items()
                 if grp['sw_cg'] == 'yes'}

    # sw hint clocks
    hint_clks = {clk:src for grp in grps for (clk,src) in grp['clocks'].items()
                 if grp['sw_cg'] == 'hint'}


    # generate hjson
    hjson_out.write_text(
         hjson_tpl.render(cfg=topcfg,
                          ft_clks=ft_clks,
                          rg_clks=rg_clks,
                          sw_clks=sw_clks,
                          hint_clks=hint_clks))

    # generate rtl package
    pkg_out.write_text(
         pkg_tpl.render(cfg=topcfg,
                        ft_clks=ft_clks,
                        rg_clks=rg_clks,
                        sw_clks=sw_clks,
                        hint_clks=hint_clks))

    # generate top level
    rtl_out.write_text(
         rtl_tpl.render(cfg=topcfg,
                          ft_clks=ft_clks,
                          rg_clks=rg_clks,
                          sw_clks=sw_clks,
                          hint_clks=hint_clks))


if __name__ == "__main__":
    main()
