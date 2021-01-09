#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Script used to reduce the size of design for smaller FPGA devices.

This script modifies two source files to reduce the size of the design and then regenerates
all auto-generated files. The flash size is reduced in a way that does not impact the register
interface of the flash controller and is thus more or less transparent to software.
"""
import argparse
import hjson
import textwrap
import logging as log
import subprocess
import sys

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


def wrapped_docstring():
    '''Return a text-wrapped version of the module docstring'''
    paras = []
    para = []
    for line in __doc__.strip().split('\n'):
        line = line.strip()
        if not line:
            if para:
                paras.append('\n'.join(para))
                para = []
        else:
            para.append(line)
    if para:
        paras.append('\n'.join(para))

    return '\n\n'.join(textwrap.fill(p) for p in paras)


def _nexysvideo_reduce(cfg):
    log.info("Updating target to nexysvideo settings")
    log.info("Flash to 128 pages")
    log.info("Memory to 64KB")

    for mem in cfg["memory"]:
        if mem['name'] == 'eflash':
            mem['pages_per_bank'] = 128
        if mem['name'] == 'ram_main':
            mem['size'] = '0x10000'

def main():

    # Display INFO log messages and up.
    log.basicConfig(level=log.INFO, format="%(levelname)s: %(message)s")

    parser = argparse.ArgumentParser(
        prog="fpga_size_reduce",
        description=wrapped_docstring(),
        formatter_class=argparse.RawDescriptionHelpFormatter)

    parser.add_argument(
        '--toppath',
        '-t',
        default='.',
        help='provide top path.')

    parser.add_argument(
        '--target',
        '-g',
        default='nexysvideo',
        choices=['nexysvideo'],
        help='fpga reduction target')

    parser.add_argument(
        '--build',
        '-b',
        default=False,
        action='store_true',
        help='Build ROM based on reduced design')

    args = parser.parse_args()

    # Get path to top-level directory
    top_path = args.toppath
    top_hjson = top_path + '/hw/top_earlgrey/data/top_earlgrey.hjson'
    orig_hjson = top_hjson + '.orig'

    # Modify hjson to change flash size
    with open(top_hjson, "r") as hjson_file:
        cfg = hjson.load(hjson_file,
                         use_decimal=True)

    # write out original version reformatted
    with open(orig_hjson, "w") as hjson_file:
        hjson_file.write(orighdr + hjson.dumps(cfg, hjson_file))

    # update value based on target selection
    globals()["_{}_reduce".format(args.target)](cfg)

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
    if (args.build):
        log.info("Regenerating boot ROM...")
        cmd = ["ninja", "-C", top_path + "/build-out",
               "sw/device/boot_rom/boot_rom_export_fpga_nexysvideo"]
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
