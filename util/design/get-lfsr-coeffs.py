#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import shutil
import subprocess
import sys
import wget

USAGE = """./get_lfsr_coeffs.py [-t <temporary folder>] [-o <outfile>] [-f] [--pdf <pdf file>]

Downloads LFSR constants from [1] and dumps them in SystemVerilog format (for
use in prim_lfsr.sv). These coeffs are for a Galois XOR type LFSR, and cover
implementations ranging from 4 to 64bits.

Alternatively, the script can also extract the XNOR Fibonacci type LFSR
coefficients from the Xilinx application note 52 [2] by specifying the --pdf
<pdf file> switch. The pdf has to be downloaded manually from [2] first. Note
that this depends on the pdftotext utility for Linux.

[1] https://users.ece.cmu.edu/~koopman/lfsr/

[2] https://docs.xilinx.com/v/u/en-US/xapp052
"""

# configuration for [1]
MIN_LFSR_LEN = 4
MAX_LFSR_LEN = 64
BASE_URL = 'https://users.ece.cmu.edu/~koopman/lfsr/'

# configuration for [2]
LINE_FILTER = [
    'Table 3: Taps for Maximum-Length LFSR Counters',
    'XAPP 052 July 7,1996 (Version 1.1)'
]


# helper function to write out coeffs
def dump_coeffs(widths, coeffs, outfile):
    # widths consistency check
    for k in range(widths[0], widths[-1] + 1):
        # print("%d -- %d" % (k,widths[k-widths[0]]))
        if k != widths[k - widths[0]]:
            print("Error: widths is not consistently increasing")
            sys.exit(1)

    # select first coefficient in each file and print to SV LUT
    with outfile:
        decl_str = "localparam int unsigned LUT_OFF = %d;\n" \
            % (min(widths))
        outfile.write(decl_str)
        decl_str = "localparam logic [%d:0] LFSR_COEFFS [%d] = '{ " \
            % (max(widths) - 1, max(widths) - min(widths) + 1)
        outfile.write(decl_str)
        comma = ',\n'
        spaces = ''
        for k in widths:
            if k == max(widths):
                comma = ""
            if k == min(widths) + 1:
                spaces += ' ' * len(decl_str)
            outfile.write("%s%d'h%s%s" %
                          (spaces, max(widths), coeffs[k - widths[0]], comma))
        outfile.write(' };\n')


# converts list with bit positions to a hex bit mask string
def to_bit_mask(bitPositions):

    bitMask = 0
    for b in bitPositions:
        bitMask += 2**(b - 1)

    return "%X" % bitMask


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
        help="""Temporary folder to download the lfsr constant files
                to (defaults to ./lfsr_tmp)""",
        default='lfsr_tmp')
    parser.add_argument('--pdf',
                        type=str,
                        help="""Path to Xilinx Application Note 052 with
                                primitive polynomial coefficients.""",
                        )
    parser.add_argument('-f',
                        '--force',
                        help='Overwrite tempfolder.',
                        action='store_true')
    parser.add_argument('-o',
                        '--output',
                        type=argparse.FileType('w'),
                        default=sys.stdout,
                        metavar='file',
                        help='Output file (default stdout)')

    args = parser.parse_args()

    if args.force and os.path.exists(args.tempfolder):
        shutil.rmtree(args.tempfolder)

    if not os.path.exists(args.tempfolder):
        os.makedirs(args.tempfolder, exist_ok=args.force)

        if args.pdf:
            pdf_path = os.path.abspath(args.pdf)

            if not os.path.isfile(pdf_path):
                print("File %s does not exist" % pdf_path)
                sys.exit(1)

            os.chdir(args.tempfolder)
            cmd = ['pdftotext %s %s/xapp052.txt' %
                   (pdf_path, os.getcwd())]
            subprocess.call(cmd, shell=True)
            print("")
            cmd = ['grep -A 350 "%s" xapp052.txt > table.txt' % LINE_FILTER[0]]
            subprocess.call(cmd, shell=True)

            # parse the table
            widths = []
            coeffs = []
            columnType = 0
            with open('table.txt') as infile:
                for line in infile:
                    line = line.strip()
                    if line and line not in LINE_FILTER:
                        if line == 'n':
                            columnType = 0
                        # yes, this is a typo in the PDF :)
                        elif line == 'XNOR from':
                            columnType = 1
                        elif columnType:
                            tmpCoeffs = [int(c) for c in line.split(',')]
                            coeffs += [tmpCoeffs]
                        else:
                            widths += [int(line)]

            # # printout for checking
            # for (w,c) in zip(widths,coeffs):
            #     print("width: %d > coeffs: %s" % (w, str(c)))

            # convert to bitmask
            for k in range(len(coeffs)):
                coeffs[k] = to_bit_mask(coeffs[k])

        else:
            os.chdir(args.tempfolder)

            for k in range(MIN_LFSR_LEN, MAX_LFSR_LEN + 1):
                url = '%s%d.txt' % (BASE_URL, k)
                print("\nDownloading %d bit LFSR coeffs from %s..." % (k, url))
                wget.download(url)
            print("")

            widths = []
            coeffs = []
            for k in range(MIN_LFSR_LEN, MAX_LFSR_LEN + 1):
                filename = '%d.txt' % k
                with open(filename) as infile:
                    # read the first line
                    widths += [k]
                    coeffs += [infile.readline().strip()]

        # write to stdout or file
        dump_coeffs(widths, coeffs, outfile=args.output)
    else:
        print("Temporary directory already exists, abort...")
        sys.exit(1)


if __name__ == '__main__':
    main()
