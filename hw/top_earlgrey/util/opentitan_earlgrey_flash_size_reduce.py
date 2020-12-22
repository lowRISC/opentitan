#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Script used to reduce the size of the embedded flash for smaller FPGA devices.

This script modifies two source files to reduce the size of the embedded flash and then regenerates
all auto-generated files. The flash size is reduced in a way that does not impact the register
interface of the flash controller and is thus more or less transparent to software.
"""

import hjson
import logging as log
import subprocess
import sys
import os
import re

# Display INFO log messages and up.
log.basicConfig(level=log.INFO, format="%(levelname)s: %(message)s")

hdr = '''// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
'''

orighdr = hdr + '''
// This file has been automatically created from top_earlgrey.hjson.
// This is a reformatted copy of top_earlgrey.hjson
'''

genhdr = hdr + '''
// This file has been automatically modified to reduce the size of the flash.
// To see what has been changed, please compare to top_earlgrey.original.hjson.
'''

def main():

    # Get path to top-level directory
    top_path = os.path.normpath(os.path.join(os.path.dirname(__file__), "../../.."))
    top_hjson = top_path + "/hw/top_earlgrey/data/top_earlgrey.hjson"

    # Modify hjson to change flash size
    with open(top_hjson, "r") as hjson_file:
        cfg = hjson.load(hjson_file,
                         use_decimal=True)

    # write out original version reformatted
    with open(top_path + "/hw/top_earlgrey/data/top_earlgrey.original.hjson", "w") as hjson_file:
         hjson_file.write(orighdr + hjson.dumps(cfg, hjson_file))

    # update value
    log.info("Updating flash pages_per_bank to 16")
    for mem in cfg["memory"]:
        if mem['type'] == 'eflash':
            mem['pages_per_bank'] = 16

    # write back updated hjson
    with open(top_hjson, "w") as hjson_file:
        hjson_file.write(genhdr + hjson.dumps(cfg, hjson_file))

    # Regenerate auto-generated files
    print("Regenerating all auto-generated files...")
    cmd = ["make", "-C", top_path + "/hw"]
    try:
        subprocess.run(cmd,
                       check=True,
                       stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT,
                       universal_newlines=True)

    except subprocess.CalledProcessError as e:
        log.error("Failed to regenerate auto-generated files: " + str(e))
        log.error(e.stdout)
        sys.exit(1)

    # Regenerate boot ROM
    print("Regenerating boot ROM...")
    cmd = ["ninja", "-C", top_path + "/build-out", "sw/device/boot_rom/boot_rom_export_fpga_nexysvideo"]
    try:
        subprocess.run(cmd,
                       check=True,
                       stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT,
                       universal_newlines=True)

    except subprocess.CalledProcessError as e:
        log.error("Failed to regenerate boot ROM: " + str(e))
        log.error(e.stdout)
        sys.exit(1)

    return 0


if __name__ == "__main__":
    sys.exit(main())
