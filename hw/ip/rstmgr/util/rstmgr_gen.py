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

    hjson_tpl = Template(filename=str(current / '../data/rstmgr.hjson.tpl'))
    rtl_tpl   = Template(filename=str(current / '../data/rstmgr.sv.tpl'))
    pkg_tpl   = Template(filename=str(current / '../data/rstmgr_pkg.sv.tpl'))

    hjson_out = current / '../data/rstmgr.hjson'
    rtl_out   = current / '../rtl/rstmgr.sv'
    pkg_out   = current / '../rtl/rstmgr_pkg.sv'

    cfgpath   = current / '../data/rstmgr.cfg.example.hjson'

    try:
        with open(cfgpath, 'r') as cfg:
            topcfg = hjson.load(cfg,use_decimal=True,object_pairs_hook=OrderedDict)
    except ValueError:
        log.error("{} not found".format(cfgpath))
        raise SystemExit(sys.exc_info()[1])

    clks = []
    output_rsts = OrderedDict()
    por_rsts = OrderedDict()
    sw_rsts = OrderedDict()
    leaf_rsts = OrderedDict()

    # unique clocks
    for rst in topcfg["resets"]:
        if rst['type'] != "ext" and rst['clk'] not in clks:
            clks.append(rst['clk'])

    # resets sent to reset struct
    output_rsts = [rst for rst in topcfg["resets"] if rst['type'] == "top"]

    # por_rsts = [rst for rst in topcfg["resets"] if 'inst' in rst and rst['inst'] == "por"]

    # sw controlled resets
    sw_rsts = [rst for rst in topcfg["resets"] if 'sw' in rst and rst['sw'] == 1]

    # leaf resets
    leaf_rsts = [rst for rst in topcfg["resets"] if rst['gen'] == 1]

    # generate hjson
    hjson_out.write_text(
         hjson_tpl.render(cfg=topcfg,
                          clks=clks,
                          sw_rsts=sw_rsts))

    # generate rtl package
    pkg_out.write_text(
         pkg_tpl.render(cfg=topcfg,
                        output_rsts=output_rsts))

    # generate top level
    rtl_out.write_text(
         rtl_tpl.render(cfg=topcfg,
                        clks=clks,
                        leaf_rsts=leaf_rsts))


if __name__ == "__main__":
    main()
