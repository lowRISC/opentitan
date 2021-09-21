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


class Flash:
    """Flash class contains information regarding parameter defaults.
       For now, only expose banks / pages_per_bank for user configuration.
       For now, also enforce power of 2 requirement.
    """
    max_banks = 4
    max_pages_per_bank = 1024

    def __init__(self, mem, base_addr):
        self.base_addr = int(base_addr, 16)
        self.banks = mem.get('banks', 2)
        self.pages_per_bank = mem.get('pages_per_bank', 8)
        self.program_resolution = mem.get('program_resolution', 128)
        self.words_per_page = 256
        self.data_width = 64
        self.metadata_width = 12
        self.info_types = 3
        self.infos_per_bank = [10, 1, 2]
        self.word_bytes = int(self.data_width / 8)
        self.pgm_resolution_bytes = int(self.program_resolution * self.word_bytes)
        self.check_values()

        # populate size variable
        self.bytes_per_page = self.word_bytes * self.words_per_page
        self.bytes_per_bank = self.bytes_per_page * self.pages_per_bank
        self.total_bytes = self.bytes_per_bank * self.banks

        size_int = int(self.total_bytes)
        self.size = hex(size_int)
        self.end_addr = self.base_addr + size_int

    def is_pow2(self, n):
        return (n != 0) and (n & (n - 1) == 0)

    def check_values(self):
        pow2_check = (self.is_pow2(self.banks) and
                      self.is_pow2(self.pages_per_bank) and
                      self.is_pow2(self.program_resolution))
        limit_check = ((self.banks <= Flash.max_banks) and
                       (self.pages_per_bank <= Flash.max_pages_per_bank))

        if not pow2_check:
            raise ValueError(f'flash power of 2 check failed. A supplied parameter '
                             'is not power of 2')

        if not limit_check:
            raise ValueError(f'flash number of banks and pages per bank too large')


# Common header for generated files
def main():

    current = Path(__file__).parent.absolute()

    hjson_tpl = Template(filename=str(current / '../data/flash_ctrl.hjson.tpl'))
    region_cfg_tpl = Template(filename=str(current / '../data/flash_ctrl_region_cfg.sv.tpl'))
    rtl_tpl = Template(filename=str(current / '../data/flash_ctrl.sv.tpl'))
    pkg_tpl = Template(filename=str(current / '../data/flash_ctrl_pkg.sv.tpl'))

    hjson_out = current / '../data/flash_ctrl.hjson'
    region_cfg_out = current / '../rtl/flash_ctrl_region_cfg.sv'
    rtl_out = current / '../rtl/flash_ctrl.sv'
    pkg_out = current / '../rtl/flash_ctrl_pkg.sv'
    cfgpath = current / '../../../top_earlgrey/data/autogen/top_earlgrey.gen.hjson'

    try:
        with open(cfgpath, 'r') as cfg:
            topcfg = hjson.load(cfg, use_decimal=True, object_pairs_hook=OrderedDict)
    except ValueError:
        log.error("{} not found".format(cfgpath))
        raise SystemExit(sys.exc_info()[1])


    flash_mems = [module for module in topcfg['module'] if module['type'] == 'flash_ctrl']
    if len(flash_mems) > 1:
        log.error("This design does not currently support multiple flashes")
        return

    cfg = Flash(flash_mems[0]['memory']['mem']['config'],
                flash_mems[0]['base_addrs']['mem'])

    # generate hjson
    hjson_out.write_text(hjson_tpl.render(cfg=cfg))

    # generate rtl package
    pkg_out.write_text(pkg_tpl.render(cfg=cfg))

    # generate reg wrap
    region_cfg_out.write_text(region_cfg_tpl.render(cfg=cfg))

    # generate top level
    rtl_out.write_text(rtl_tpl.render(cfg=cfg))


if __name__ == "__main__":
    main()
