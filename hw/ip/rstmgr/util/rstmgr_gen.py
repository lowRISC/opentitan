#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Reset Manager Generator
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

    cfgpath   = current / '../../../top_earlgrey/data/autogen/top_earlgrey.gen.hjson'

    try:
        with open(cfgpath, 'r') as cfg:
            topcfg = hjson.load(cfg,use_decimal=True,object_pairs_hook=OrderedDict)
    except ValueError:
        log.error("{} not found".format(cfgpath))
        raise SystemExit(sys.exc_info()[1])

    # Parameters needed for generation
    clks = []
    output_rsts = OrderedDict()
    sw_rsts = OrderedDict()
    leaf_rsts = OrderedDict()

    # unique clocks
    for rst in topcfg["resets"]["nodes"]:
        if rst['type'] != "ext" and rst['clk'] not in clks:
            clks.append(rst['clk'])

    # resets sent to reset struct
    output_rsts = [rst for rst in topcfg["resets"]["nodes"] if rst['type'] == "top"]

    # sw controlled resets
    sw_rsts = [rst for rst in topcfg["resets"]["nodes"] if 'sw' in rst and rst['sw'] == 1]

    # leaf resets
    leaf_rsts = [rst for rst in topcfg["resets"]["nodes"] if rst['gen']]

    log.info("output resets {}".format(output_rsts))
    log.info("software resets {}".format(sw_rsts))
    log.info("leaf resets {}".format(leaf_rsts))

    # Number of reset requests
    n_rstreqs = len(topcfg["reset_requests"])

    # generate hjson
    hjson_out.write_text(
         hjson_tpl.render(clks=clks,
                          power_domains=topcfg['power']['domains'],
                          num_rstreqs=n_rstreqs,
                          sw_rsts=sw_rsts,
                          output_rsts=output_rsts,
                          leaf_rsts=leaf_rsts,
                          export_rsts=topcfg['exported_rsts']))

    # generate rtl package
    pkg_out.write_text(
        pkg_tpl.render(clks=clks,
                       power_domains=topcfg['power']['domains'],
                       num_rstreqs=n_rstreqs,
                       sw_rsts=sw_rsts,
                       output_rsts=output_rsts,
                       leaf_rsts=leaf_rsts,
                       export_rsts=topcfg['exported_rsts']))

    # generate top level
    rtl_out.write_text(
         rtl_tpl.render(clks=clks,
                        power_domains=topcfg['power']['domains'],
                        num_rstreqs=n_rstreqs,
                        sw_rsts=sw_rsts,
                        output_rsts=output_rsts,
                        leaf_rsts=leaf_rsts,
                        export_rsts=topcfg['exported_rsts']))


if __name__ == "__main__":
    main()
