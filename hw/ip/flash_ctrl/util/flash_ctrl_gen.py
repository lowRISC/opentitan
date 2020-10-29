#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Flash Controller Generator
"""

import logging as log
import sys
from collections import OrderedDict
from pathlib import Path

import hjson
from mako.template import Template


# Common header for generated files
def main():

    current = Path(__file__).parent.absolute()

    hjson_tpl = Template(filename=str(current / '../data/flash_ctrl.hjson.tpl'))
    rtl_tpl = Template(filename=str(current / '../data/flash_ctrl.sv.tpl'))
    pkg_tpl = Template(filename=str(current / '../data/flash_ctrl_pkg.sv.tpl'))

    hjson_out = current / '../data/flash_ctrl.hjson'
    rtl_out = current / '../rtl/flash_ctrl.sv'
    pkg_out = current / '../rtl/flash_ctrl_pkg.sv'
    cfgpath = current / '../../../top_earlgrey/data/autogen/top_earlgrey.gen.hjson'

    try:
        with open(cfgpath, 'r') as cfg:
            topcfg = hjson.load(cfg, use_decimal=True, object_pairs_hook=OrderedDict)
    except ValueError:
        log.error("{} not found".format(cfgpath))
        raise SystemExit(sys.exc_info()[1])

    flash_mems = [mem for mem in topcfg['memory'] if mem['type'] == 'eflash']
    if len(flash_mems) > 1:
        log.error("This design does not currently support multiple flashes")
        return

    cfg = flash_mems[0]

    # generate hjson
    hjson_out.write_text(hjson_tpl.render(cfg=cfg))

    # generate rtl package
    pkg_out.write_text(pkg_tpl.render(cfg=cfg))

    # generate top level
    rtl_out.write_text(rtl_tpl.render(cfg=cfg))


if __name__ == "__main__":
    main()
