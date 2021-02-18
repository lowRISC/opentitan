#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""SECDED encoder/decoder generator

Current version doesn't optimize Fan-In. It uses Hsiao code (modified version
of Hamming code + parity). Please refer https://arxiv.org/pdf/0803.1217.pdf

For some further background and info on the differences between Hamming and
Hsiao SECDED codes, refer to https://ieeexplore.ieee.org/document/8110065.g
"""

import argparse
import itertools
import logging as log
import math
import random

COPYRIGHT = """// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
"""
CODE_OPTIONS = ['hsiao', 'hamming']


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


def calc_bitmasks(k, m, codes, dec):
    # Transform fanin indices into bitmask.
    fanin_masks = [0] * m
    for i, c in enumerate(codes):
        for j in c:
            fanin_masks[j] += 1 << i
    # For decode ops, include ECC bit position.
    if dec:
        for j in range(m):
            fanin_masks[j] += 1 << (k + j)
    return fanin_masks


def print_enc(n, k, m, codes):
    outstr = "  always_comb begin : p_encode\n"
    outstr += "    out = {}'(in);\n".format(n)
    format_str = "    out[{}] = ^(out & " + str(n) + "'h{:0" + str(
        (n + 3) // 4) + "X});\n"
    # Print parity computation
    for j, mask in enumerate(calc_bitmasks(k, m, codes, False)):
        outstr += format_str.format(j + k, mask)
    outstr += "  end\n"
    return outstr


def calc_syndrome(code):
    log.info("in syndrome {}".format(code))
    return sum(map((lambda x: 2**x), code))


def print_dec(n, k, m, codes, codetype):
    outstr = ""
    outstr += "\n"
    outstr += "  // Syndrome calculation\n"
    format_str = "  assign syndrome_o[{}] = ^(in & " + str(n) + "'h{:0" + str(
        (n + 3) // 4) + "X});\n"
    # Print syndrome computation
    for j, mask in enumerate(calc_bitmasks(k, m, codes, True)):
        outstr += format_str.format(j, mask)
    outstr += "\n"
    outstr += "  // Corrected output calculation\n"
    for i in range(k):
        outstr += "  assign d_o[%d] = (syndrome_o == %d'h%x) ^ in[%d];\n" % (
            i, m, calc_syndrome(codes[i]), i)
    outstr += "\n"
    outstr += "  // err_o calc. bit0: single error, bit1: double error\n"
    # The Hsiao and Hamming syndromes are interpreted slightly differently.
    if codetype == "hamming":
        outstr += "  assign err_o[0] = syndrome_o[%d];\n" % (m - 1)
        outstr += "  assign err_o[1] = |syndrome_o[%d:0] & ~syndrome_o[%d];\n" % (
            m - 2, m - 1)
    else:
        outstr += "  assign err_o[0] = ^syndrome_o;\n"
        outstr += "  assign err_o[1] = ~err_o[0] & (|syndrome_o);\n"
    return outstr


# return whether an integer is a power of 2
def is_pow2(n):
    return (n & (n - 1) == 0) and n != 0


def is_odd(n):
    return (n % 2) > 0


# k = data bits
# m = parity bits
# generate hsiao code
def hsiao_code(k, m):
    # using itertools combinations, generate odd number of 1 in a row

    required_row = k  # k rows are needed, decreasing everytime when it acquite

    fanin_ideal = ideal_fanin(k, m)
    log.info("Ideal Fan-In value: %d" % fanin_ideal)

    # Each entry represents a row in below parity matrix
    # Entry is tuple and the value inside is the position of ones
    # e.g. (0,1,2) in m:=7
    # row -> [1 1 1 0 0 0 0]
    codes = []

    # Find code matrix =======================================================
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
            # Find optimized fan-in ==========================================

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

    log.info("Hsiao codes {}".format(codes))
    return codes


# n = total bits
# k = data bits
# m = parity bits
# generate hamming code
def hamming_code(n, k, m):

    # construct a list of code tuples.
    # Tuple corresponds to each bit position and shows which parity bit it participates in
    # Only the data bits are shown, the parity bits are not.
    codes = []
    for pos in range(1, n + 1):
        # this is a valid parity bit position or the final parity bit
        if (is_pow2(pos) or pos == n):
            continue
        else:
            code = ()
            for p in range(m):

                # this is the starting parity position
                parity_pos = 2**p

                # back-track to the closest parity bit multiple and see if it is even or odd
                # If even, we are in the skip phase, do not include
                # If odd, we are in the include phase
                parity_chk = int((pos - (pos % parity_pos)) / parity_pos)
                log.debug("At position {} parity value {}, {}".format(
                    pos, parity_pos, parity_chk))

                # valid for inclusion or final parity bit that includes everything
                if is_odd(parity_chk) or p == m - 1:
                    code = code + (p, )
                    log.info("add {} to tuple {}".format(p, code))

            codes.append(code)

    # final parity bit includes all ECC bits
    for p in range(m - 1):
        codes.append((m - 1, ))

    log.info("Hamming codes {}".format(codes))
    return codes


def write_enc_dec_files(n, k, m, s, codes, suffix, outdir, codetype):
    enc_out = print_enc(n, k, m, codes)

    module_name = "prim_secded%s_%d_%d" % (suffix, n, k)

    with open(outdir + "/" + module_name + "_enc.sv", "w") as f:
        outstr = '''{}// SECDED Encoder generated by
// util/design/secded_gen.py -m {} -k {} -s {} -c {}

module {}_enc (
  input        [{}:0] in,
  output logic [{}:0] out
);

{}
endmodule : {}_enc
'''.format(COPYRIGHT, m, k, s, codetype, module_name, (k - 1), (n - 1),
           enc_out, module_name)
        f.write(outstr)

    dec_out = print_dec(n, k, m, codes, codetype)

    with open(outdir + "/" + module_name + "_dec.sv", "w") as f:
        outstr = '''{}// SECDED Decoder generated by
// util/design/secded_gen.py -m {} -k {} -s {} -c {}

module {}_dec (
  input        [{}:0] in,
  output logic [{}:0] d_o,
  output logic [{}:0] syndrome_o,
  output logic [1:0] err_o
);

{}
endmodule : {}_dec
'''.format(COPYRIGHT, m, k, s, codetype, module_name, (n - 1), (k - 1),
           (m - 1), dec_out, module_name)
        f.write(outstr)


def write_fpv_files(n, k, m, codes, suffix, outdir):
    module_name = "prim_secded%s_%d_%d" % (suffix, n, k)

    with open(outdir + "/tb/" + module_name + "_fpv.sv", "w") as f:
        outstr = '''{}// SECDED FPV testbench generated by util/design/secded_gen.py

module {}_fpv (
  input               clk_i,
  input               rst_ni,
  input        [{}:0] in,
  output logic [{}:0] d_o,
  output logic [{}:0] syndrome_o,
  output logic [1:0]  err_o,
  input        [{}:0] error_inject_i
);

  logic [{}:0] data_enc;

  {}_enc {}_enc (
    .in,
    .out(data_enc)
  );

  {}_dec {}_dec (
    .in(data_enc ^ error_inject_i),
    .d_o,
    .syndrome_o,
    .err_o
  );

endmodule : {}_fpv
'''.format(COPYRIGHT, module_name, (k - 1), (k - 1), (m - 1), (n - 1), (n - 1),
           module_name, module_name, module_name, module_name, module_name)
        f.write(outstr)

    with open(outdir + "/vip/" + module_name + "_assert_fpv.sv", "w") as f:
        outstr = '''{}// SECDED FPV assertion file generated by util/design/secded_gen.py

module {}_assert_fpv (
  input        clk_i,
  input        rst_ni,
  input [{}:0] in,
  input [{}:0] d_o,
  input [{}:0] syndrome_o,
  input [1:0]  err_o,
  input [{}:0] error_inject_i
);

  // Inject a maximum of two errors simultaneously.
  `ASSUME_FPV(MaxTwoErrors_M, $countones(error_inject_i) <= 2)
  // This bounds the input data state space to make sure the solver converges.
  `ASSUME_FPV(DataLimit_M, $onehot0(in) || $onehot0(~in))
  // Single bit error detection
  `ASSERT(SingleErrorDetect_A, $countones(error_inject_i) == 1 |-> err_o[0])
  `ASSERT(SingleErrorDetectReverse_A, err_o[0] |-> $countones(error_inject_i) == 1)
  // Double bit error detection
  `ASSERT(DoubleErrorDetect_A, $countones(error_inject_i) == 2 |-> err_o[1])
  `ASSERT(DoubleErrorDetectReverse_A, err_o[1] |-> $countones(error_inject_i) == 2)
  // Single bit error correction (implicitly tests the syndrome output)
  `ASSERT(SingleErrorCorrect_A, $countones(error_inject_i) < 2 |-> in == d_o)
  // Basic syndrome check
  `ASSERT(SyndromeCheck_A, |syndrome_o |-> $countones(error_inject_i) > 0)
  `ASSERT(SyndromeCheckReverse_A, $countones(error_inject_i) > 0 |-> |syndrome_o)

endmodule : {}_assert_fpv
'''.format(COPYRIGHT, module_name, (k - 1), (k - 1), (m - 1), (n - 1),
           module_name)
        f.write(outstr)

    with open(outdir + "/tb/" + module_name + "_bind_fpv.sv", "w") as f:
        outstr = '''{}// SECDED FPV bind file generated by util/design/secded_gen.py

module {}_bind_fpv;

  bind {}_fpv
    {}_assert_fpv {}_assert_fpv (
    .clk_i,
    .rst_ni,
    .in,
    .d_o,
    .syndrome_o,
    .err_o,
    .error_inject_i
  );

endmodule : {}_bind_fpv
'''.format(COPYRIGHT, module_name, module_name, module_name, module_name,
           module_name)
        f.write(outstr)

    with open(outdir + "/" + module_name + "_fpv.core", "w") as f:
        outstr = '''CAPI=2:
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: "lowrisc:fpv:{}_fpv:0.1"
description: "SECDED FPV target"
filesets:
  files_formal:
    depend:
      - lowrisc:prim:all
      - lowrisc:prim:secded
    files:
      - vip/{}_assert_fpv.sv
      - tb/{}_fpv.sv
      - tb/{}_bind_fpv.sv
    file_type: systemVerilogSource

targets:
  default: &default_target
    # note, this setting is just used
    # to generate a file list for jg
    default_tool: icarus
    filesets:
      - files_formal
    toplevel:
      - {}_fpv

  formal:
    <<: *default_target

  lint:
    <<: *default_target

'''.format(module_name, module_name, module_name, module_name, module_name)
        f.write(outstr)


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
        'Parity length. If fan-in is too big, increasing m helps. (default: %(default)s)'
    )
    parser.add_argument(
        '-k',
        type=int,
        default=32,
        help=
        'Code length. Minimum \'m\' is calculated by the tool (default: %(default)s)'
    )
    parser.add_argument(
        '-c',
        default='hsiao',
        help='ECC code used. Options: hsiao / hamming (default: %(default)s)')
    parser.add_argument('-s',
                        type=int,
                        metavar='<seed>',
                        help='Custom seed for RNG.')
    parser.add_argument('--no_fpv',
                        action='store_true',
                        help='Do not generate FPV testbench.')
    parser.add_argument('--outdir',
                        default='hw/ip/prim/rtl/',
                        help='''
        Output directory. The output file will be named
        `prim_secded_<n>_<k>_enc/dec.sv` (default: %(default)s)
        ''')
    parser.add_argument('--fpv_outdir',
                        default='hw/ip/prim/fpv/',
                        help='''
        FPV output directory. The output files will have
        the base name `prim_secded_<n>_<k>_*_fpv` (default: %(default)s)
        ''')
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
        log.warning(
            "given \'m\' argument is smaller than minimum requirement " +
            "using calculated minimum")
        m = min_m
    else:
        m = args.m

    n = m + k
    log.info("n(%d), k(%d), m(%d)", n, k, m)

    if args.s is None:
        random.seed()
        args.s = random.getrandbits(32)

    # If no seed has been provided, we choose a seed and print it
    # into the generated output later on such that this run can be
    # reproduced.
    if args.s is None:
        random.seed()
        args.s = random.getrandbits(32)

    random.seed(args.s)

    # Error check code selection
    codes = []
    suffix = ''
    if (args.c == 'hsiao'):
        codes = hsiao_code(k, m)
    elif (args.c == 'hamming'):
        suffix = '_hamming'
        codes = hamming_code(n, k, m)
    else:
        log.error("Invalid code {} selected, use one of {}".format(
            args.c, CODE_OPTIONS))
        return

    write_enc_dec_files(n, k, m, args.s, codes, suffix, args.outdir, args.c)

    # Print out FPV testbench by default.
    if not args.no_fpv:
        write_fpv_files(n, k, m, codes, suffix, args.fpv_outdir)


if __name__ == "__main__":
    main()
