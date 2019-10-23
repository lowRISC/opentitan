#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""SECDED encoder/decoder generator

Current version doesn't optimize Fan-In. It uses Hsiao code (modified version
of Hamming code + parity). Please refer https://arxiv.org/pdf/0803.1217.pdf
"""

import argparse
import itertools
import logging as log
import math
import os
import random
import sys
import time
from pathlib import PurePath

COPYRIGHT = """// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
"""


def min_paritysize(k):
    # SECDED --> Hamming distance 'd': 4
    # 2^(m-1) should cover (m+k)
    for m in range(2, 10):
        if 2**m >= (k + m + 1):
            return m + 1
    return -1


def ideal_fanin(k, m):
    """Compute Ideal Max Fanin of any bit in the ecc codes."""
    fanin = 0
    needed = k
    for select in range(3, m + 1, 2):
        combinations = list(itertools.combinations(range(m), select))
        if len(combinations) <= needed:
            fanin += int(math.ceil(float(len(combinations) * select) / m))
            needed -= len(combinations)
        else:
            fanin += int(math.ceil(float(needed * select) / m))
            needed = 0
        if not needed:
            break
    return fanin


def print_comb(n, k, m, cur_m, codes, start_cnt):
    outstr = ""
    cnt = start_cnt
    first = True
    for j in range(k):
        if cnt == 7:
            cnt = 0
            outstr += "\n"
            outstr += "                 "

        if cur_m in codes[j]:
            if not first:
                outstr += " ^"
            if first:
                first = False
            cnt += 1
            outstr += " in[%d]" % (j)
    return outstr


def print_enc(n, k, m, codes):
    outstr = ""
    for i in range(k):
        outstr += "  assign out[%d] = in[%d] ;\n" % (i, i)

    for i in range(m):
        # Print parity computation
        outstr += "  assign out[%d] =" % (i + k)
        outstr += print_comb(n, k, m, i, codes, 0)
        outstr += " ;\n"
    return outstr


def calc_syndrome(code):
    return sum(map((lambda x: 2**x), code))


def print_dec(n, k, m, codes):
    outstr = ""
    outstr += "  logic single_error;\n"
    outstr += "\n"
    outstr += "  // Syndrome calculation\n"
    for i in range(m):
        outstr += "  assign syndrome_o[%d] = in[%d] ^ " % (i, k + i)

        # Print combination
        outstr += print_comb(n, k, m, i, codes, 1)
        outstr += " ;\n"

    outstr += "\n"
    outstr += "  // Corrected output calculation\n"
    for i in range(k):
        synd_v = calc_syndrome(codes[i])
        outstr += "  assign d_o[%d] = (syndrome_o == %d'h%x) ^ in[%d];\n" % (
            i, m, calc_syndrome(codes[i]), i)
    outstr += "\n"
    outstr += "  // err_o calc. bit0: single error, bit1: double error\n"
    outstr += "  assign single_error = ^syndrome_o;\n"
    outstr += "  assign err_o[0] =  single_error;\n"
    outstr += "  assign err_o[1] = ~single_error & (|syndrome_o);\n"
    return outstr


def main():
    parser = argparse.ArgumentParser(
        prog="secded_gen",
        description='''This tool generates Single Error Correction Double Error
        Detection(SECDED) encoder and decoder modules in SystemVerilog.
        ''')
    parser.add_argument(
        '-m',
        type=int,
        default=7,
        help=
        'parity length. If fan-in is too big, increasing m helps. (default: %(default)s)'
    )
    parser.add_argument(
        '-k',
        type=int,
        default=32,
        help=
        'code length. Minimum \'m\' is calculated by the tool (default: %(default)s)'
    )
    parser.add_argument(
        '--outdir',
        default='../rtl',
        help=
        'output directory. The output file will be named `prim_secded_<n>_<k>_enc/dec.sv` (default: %(default)s)'
    )
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose')

    args = parser.parse_args()

    if (args.verbose):
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(levelname)s: %(message)s")

    # Error checking
    if (args.k <= 1 or args.k > 120):
        log.error("Current tool doesn't support the value k (%d)", args.k)
    k = args.k

    if (args.m <= 1 or args.m > 20):
        log.error("Current tool doesn't support the value m (%d)", args.m)

    # Calculate 'm' (parity size)
    min_m = min_paritysize(k)
    if (args.m < min_m):
        log.error("given \'m\' argument is smaller than minimum requirement")
        m = min_m
    else:
        m = args.m

    n = m + k
    log.info("n(%d), k(%d), m(%d)", n, k, m)

    random.seed(time.time())

    # using itertools combinations, generate odd number of 1 in a row

    required_row = k  # k rows are needed, decreasing everytime when it acquite

    fanin_ideal = ideal_fanin(k, m)
    log.info("Ideal Fan-In value: %d" % fanin_ideal)

    codes = []

    for step in range(3, m + 1, 2):
        # starting from 3 as I matrix represents data
        # Increased by 2 as number of 1 should be even in a row (odd excluding I)

        # get the list of combinations
        candidate = list(itertools.combinations(range(m), step))

        # Let's shuffle
        random.shuffle(candidate)

        if len(candidate) <= required_row:
            # we need more round use all of them
            codes.extend(candidate)
            required_row -= len(candidate)
        else:
            # we can completed in this round
            # but search lowest fan-in codes
            # at this time, just pick lowest
            codes.extend(candidate[0:required_row])
            required_row = 0

        if required_row == 0:
            # Found everything!
            break

    log.info(codes)

    # Print Encoder
    enc_out = print_enc(n, k, m, codes)
    #log.info(enc_out)

    module_name = "prim_secded_%d_%d" % (n, k)

    with open(args.outdir + "/" + module_name + "_enc.sv", "w") as f:
        f.write(COPYRIGHT)
        f.write("// SECDED Encoder generated by secded_gen.py\n\n")

        f.write("module " + module_name + "_enc (\n")
        f.write("  input        [%d:0] in,\n" % (k - 1))
        f.write("  output logic [%d:0] out\n" % (n - 1))
        f.write(");\n\n")
        f.write(enc_out)
        f.write("endmodule\n\n")

    dec_out = print_dec(n, k, m, codes)

    with open(args.outdir + "/" + module_name + "_dec.sv", "w") as f:
        f.write(COPYRIGHT)
        f.write("// SECDED Decoder generated by secded_gen.py\n\n")

        f.write("module " + module_name + "_dec (\n")
        f.write("  input        [%d:0] in,\n" % (n - 1))
        f.write("  output logic [%d:0] d_o,\n" % (k - 1))
        f.write("  output logic [%d:0] syndrome_o,\n" % (m - 1))
        f.write("  output logic [1:0] err_o\n")
        f.write(");\n\n")
        f.write(dec_out)
        f.write("endmodule\n\n")


if __name__ == "__main__":
    main()
