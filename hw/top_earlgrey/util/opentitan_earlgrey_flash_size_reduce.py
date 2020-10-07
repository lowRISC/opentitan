#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Script used to reduce the size of the embedded flash for smaller FPGA devices.

This script modifies two source files to reduce the size of the embedded flash and then regenerates
all auto-generated files. The flash size is reduced in a way that does not impact the register
interface of the flash controller and is thus more or less transparent to software.
"""

import logging as log
import subprocess
import sys
import os
import re

# Display INFO log messages and up.
log.basicConfig(level=log.INFO, format="%(levelname)s: %(message)s")


def main():

    # Get path to top-level directory
    top_path = os.path.normpath(os.path.join(os.path.dirname(__file__), "../../.."))

    # Change the following expressions in the following source files.
    files = [
        top_path + "/sw/device/lib/flash_ctrl.h",
        top_path + "/hw/top_earlgrey/rtl/top_pkg.sv",
        top_path + "/hw/top_earlgrey/data/top_earlgrey.hjson"
    ]
    match = [
        r"(#define\s+FLASH_PAGES_PER_BANK\s+)\d+(\s*)",
        r"(localparam\s+int\s+FLASH_PAGES_PER_BANK\s*=\s*)\d+(\s*;)",
        r"({\s*name:\s*\"eflash\"," +
        r"\s*clock_srcs:\s*{clk_i:\s*\"main\"}," +
        r"\s*clock_group:\s*\"infra\"," +
        r"\s*reset_connections:\s*{rst_ni:\s*\"lc\"}," +
        r"\s*type:\s*\"eflash\"," +
        r"\s*base_addr:\s*\"0x\w+\"," +
        r"\s*swaccess:\s*\"ro\"," +
        r"\s*size:\s*\"0x)\w+"
    ]
    replace = [
        r"\g<1>32\g<2>",  # Change FLASH_PAGES_PER_BANK to 32
        r"\g<1>32\g<2>",  # Change FLASH_PAGES_PER_BANK to 32
        r"\g<1>10000"     # Change size to 0x10000
    ]

    # Change source files
    for idx in range(len(files)):
        with open(files[idx], 'r+') as file:
            text = file.read()
            text, num = re.subn(match[idx], replace[idx], text)
            if num == 0:
                print("ERROR: Cannot find regular expression " + match[idx] +
                      " in " + files[idx] + ". "
                      "Aborting")
                sys.exit(1)
            else:
                print("Modifying " + files[idx])
                file.seek(0)
                file.write(text)
                file.truncate()

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
