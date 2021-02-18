#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Script used to check if the size of the embedded flash has already been reduced for smaller FPGA
devices.

This script checks two SystemVerilog source files (of which one is auto generated) to see if the
size of the embedded flash has been reduced.
"""

import argparse
import logging as log
import os
import sys
import re

# Display INFO log messages and up.
log.basicConfig(level=log.INFO, format="%(levelname)s: %(message)s")


def find_file(name, path):
    for root, dirs, files in os.walk(path):
        if name in files:
            return os.path.join(root, name)


def _nexysvideo_check():
    log.info("Checking nexysvideo settings")

    files = ["flash_ctrl_reg_pkg.sv", "tl_main_pkg.sv"]
    match = [
        r"parameter\s+int\s+RegPagesPerBank\s*=\s*128;",
        r"localparam\s+logic\s*\[\s*31\s*:\s*0\s*\]\s+ADDR_MASK_EFLASH\s*=\s*32'h\s*0007ffff;"
    ]

    return files, match


def main():

    parser = argparse.ArgumentParser(
        prog="flash_size_check",
        formatter_class=argparse.RawDescriptionHelpFormatter)

    parser.add_argument('--target',
                        '-g',
                        default='nexysvideo',
                        choices=['nexysvideo'],
                        help='fpga reduction target')

    args = parser.parse_args()

    # Attributes to check based on target
    files, match = globals()["_{}_check".format(args.target)]()

    # Check for the following regular expressions in the following source files.
    all_good = True
    for idx in range(len(files)):
        file_path = find_file(files[idx], "../")
        if not file_path:
            log.error("Could not find file " + files[idx] +
                      " in work directory.")
            return 1

        with open(file_path, 'r') as file:
            text = file.read()
            if not re.search(match[idx], text):
                log.info("looking at {}".format(file_path))
                all_good = False

    if not all_good:
        log.error(
            "It seems that the size of the embedded flash has not been adjusted for the " +
            "targeted FPGA device. The design might not fit. \n" +
            "Please run hw/top_earlgrey/util/top_earlgrey_reduce.py --build before " +
            "running this fusesoc core.")
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
