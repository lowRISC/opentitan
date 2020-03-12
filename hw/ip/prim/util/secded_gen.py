#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""SECDED encoder/decoder generator

Current version doesn't optimize Fan-In. It uses Hsiao code (modified version
of Hamming code + parity). Please refer https://arxiv.org/pdf/0803.1217.pdf
"""

# TODO: Add FPV assertions in the encoder/decoder module

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


def calc_fanin(width, codes):
    """Sum the ones in a column"""
    fanins = [0] * width
    log.info("Calc Code: {}".format(codes))
    for i in codes:
        for e in i:
            fanins[e] += 1

    return fanins


def print_comb(n,
               k,
               m,
               cur_m,
               codes,
               start_cnt,
               max_width=100,
               prefix="",
               first_indent=0):
    """Print XOR comb.

    @param[max_width]    Maximum Width of str
    @param[prefix]       The prepend string at the first line
    @param[first_indent] The number of character that indented at the first line
        e.g. first_indent := 2
            {prefix}in[nn] ...
                  ^ in[nn] ^ in[nn]

    result:
        {prefix}in[nn] ^ ... in[nn]
                ^ in[nn] ^ ... in[nn];
    """
    outstr = ""
    line = prefix
    prepend_len = len(prefix)
    cnt = start_cnt
    first = True
    for j in range(k):
        temp_str = ""
        if cur_m in codes[j]:
            if not first:
                temp_str += " ^"
            if first:
                first = False
            temp_str += " in[%d]" % (j)
            temp_len = len(temp_str)

            if len(line) + temp_len > max_width:
                outstr += line + "\n"
                line = ' ' * (prepend_len - first_indent) + temp_str
            else:
                line += temp_str
    outstr += line + ";\n"
    return outstr


def print_enc(n, k, m, codes):
    outstr = ""
    for i in range(k):
        outstr += "  assign out[%d] = in[%d] ;\n" % (i, i)

    for i in range(m):
        # Print parity computation
        outstr += print_comb(n, k, m, i, codes, 0, 100,
                             "  assign out[%d] =" % (i + k), 2)
    return outstr


def calc_syndrome(code):
    return sum(map((lambda x: 2**x), code))


def print_dec(n, k, m, codes):
    outstr = ""
    outstr += "  logic single_error;\n"
    outstr += "\n"
    outstr += "  // Syndrome calculation\n"
    for i in range(m):
        # Print combination
        outstr += print_comb(n, k, m, i, codes, 1, 100,
                             "  assign syndrome_o[%d] = in[%d] ^" % (i, k + i),
                             len(" in[%d] ^" % (k + i)) + 2)

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

    # Each entry represents a row in below parity matrix
    # Entry is tuple and the value inside is the position of ones
    # e.g. (0,1,2) in m:=7
    # row -> [1 1 1 0 0 0 0]
    codes = []

    ## Find code matrix =======================================================
    # This is main part to find the parity matrix.
    # For example, find SECDED for 4bit message is to find 4x4 matrix as below
    # | 1 0 0 0 x x x x |
    # | 0 1 0 0 x x x x |
    # | 0 0 1 0 x x x x |
    # | 0 0 0 1 x x x x |
    # Then message _k_ X matrix_code ==> original message with parity
    #
    # Make a row to have even number of 1 including the I matrix.
    # This helps to calculate the syndrom at the decoding stage.
    # To reduce the max fan-in, Starting with smallest number 3.
    # the number means the number of one in a row.
    # Small number of ones means smaller fan-in overall.

    for step in range(3, m + 1, 2):
        # starting from 3 as I matrix represents data
        # Increased by 2 as number of 1 should be even in a row (odd excluding I)

        # get the list of combinations [0, .., m-1] with `step`
        # e.g. step := 3 ==> [(0,1,2), (0,1,3), ... ]
        candidate = list(itertools.combinations(range(m), step))

        if len(candidate) <= required_row:
            # we need more round use all of them
            codes.extend(candidate)
            required_row -= len(candidate)
        else:
            ## Find optimized fan-in ==========================================

            # Calculate each row fan-in with current
            fanins = calc_fanin(m, codes)
            while required_row != 0:
                # Let's shuffle
                # Shuffling makes the sequence randomized --> it reduces the
                # fanin as the code takes randomly at the end of the round

                # TODO: There should be a clever way to find the subset without
                # random retrying.
                # Suggested this algorithm
                #    https://en.wikipedia.org/wiki/Assignment_problem
                random.shuffle(candidate)

                # Take a subset
                subset = candidate[0:required_row]

                subset_fanins = calc_fanin(m, subset)
                # Check if it exceeds Ideal Fan-In
                ideal = True
                for i in range(m):
                    if fanins[i] + subset_fanins[i] > fanin_ideal:
                        # Exceeded. Retry
                        ideal = False
                        break

                if ideal:
                    required_row = 0

            # Append to the code matrix
            codes.extend(subset)

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
