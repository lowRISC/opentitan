#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Utility script
Handles linear addresses generated from srec_cat to suit with fpga BRAM
architecture which need word addressing.. Example
0x0 0x00000010
0x1 0x000000FF
0x2 0x00000088

get converted to

0x0 0x00000010
0x4 0x000000FF
0x8 0x00000088 """

import argparse
import imp
import logging
import os
import sys
from pathlib import Path

DESC = """addr4x.py script handles the address generated in mem file from
srec_cat to suit with BRAM memory architecture which need word addressing"""


def main(argv):
    parser = argparse.ArgumentParser(prog="addr4x.py", description=DESC)
    parser.add_argument('--infile',
                        '-i',
                        dest='inputfile',
                        type=argparse.FileType('r', encoding='UTF-8'),
                        required=True,
                        help='Input Mem file')
    parser.add_argument('--outfile',
                        '-o',
                        dest='outputfile',
                        type=argparse.FileType('w', encoding='UTF-8'),
                        required=True,
                        help='Output Mem file')
    args = parser.parse_args()
    in_file_path = Path(args.inputfile.name).resolve()
    with open(in_file_path) as file:
        for line in file:
            if "sourceforge" not in line:
                a = line.split("@")
                b = a[1].split(" ")
                mult = int(b[0], 16)
                final = "@" + hex(mult * 4)[2:] + " " + b[1]
                args.outputfile.write(final)


if __name__ == "__main__":
    main(sys.argv)
