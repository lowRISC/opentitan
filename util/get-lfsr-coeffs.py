#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import glob
import os
import shutil
import sys

import wget

USAGE = """./get_lfsr_coeffs.py [-t <temporary folder>] [-o <outfile>] [-f]

Downloads lfsr constants from https://users.ece.cmu.edu/~koopman/lfsr/
and dumps them in SystemVerilog format (for use in prim_lfsr.sv).
"""

MIN_LFSR_LEN = 4
MAX_LFSR_LEN = 64
BASE_URL = 'https://users.ece.cmu.edu/~koopman/lfsr/'


def main():
    parser = argparse.ArgumentParser(
        prog="get-lfsr-coeffs",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        usage=USAGE,
        description=__doc__,
        epilog='defaults or the filename - can be used for stdin/stdout')
    parser.add_argument(
        '-t',
        '--tempfolder',
        help="""temporary folder to download the lfsr constant files
to (defaults to lfsr_tmp)""",
        default='lfsr_tmp')
    parser.add_argument('-f',
                        '--force',
                        help='overwrites tempfolder',
                        action='store_true')
    parser.add_argument('-o',
                        '--output',
                        type=argparse.FileType('w'),
                        default=sys.stdout,
                        metavar='file',
                        help='Output file (default stdout)')

    args = parser.parse_args()
    outfile = args.output

    if args.force and os.path.exists(args.tempfolder):
        shutil.rmtree(args.tempfolder)

    if not os.path.exists(args.tempfolder):
        # download coefficient files
        os.makedirs(args.tempfolder, exist_ok=args.force)
        os.chdir(args.tempfolder)
        for k in range(MIN_LFSR_LEN, MAX_LFSR_LEN + 1):
            url = '%s%d.txt' % (BASE_URL, k)
            print("\nDownloading %d bit LFSR coeffs from %s..." % (k, url))
            wget.download(url)
        print("")

        # select first coefficient in each file and print to SV LUT
        with outfile:
            decl_str = "localparam int unsigned LUT_OFF = %d;\n" % MIN_LFSR_LEN
            outfile.write(decl_str)
            decl_str = "localparam logic [%d:0] COEFFS [0:%d] = '{ " % (
                MAX_LFSR_LEN - 1, MAX_LFSR_LEN-MIN_LFSR_LEN)
            outfile.write(decl_str)
            comma = ',\n'
            spaces = ''
            for k in range(MIN_LFSR_LEN, MAX_LFSR_LEN + 1):
                filename = '%d.txt' % k
                with open(filename) as infile:
                    # read the first line
                    poly_coeffs = infile.readline().strip()
                    if k == MAX_LFSR_LEN:
                        comma = ""
                    if k == MIN_LFSR_LEN + 1:
                        for l in range(len(decl_str)):
                            spaces += ' '
                    outfile.write("%s%d'h%s%s" %
                                  (spaces, MAX_LFSR_LEN, poly_coeffs, comma))
            outfile.write(' };\n')
    else:
        print("Temporary directory already exists, abort...")


if __name__ == '__main__':
    main()
