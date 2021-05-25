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
import hjson
import subprocess

COPYRIGHT = """// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
"""

C_SRC_TOP = """#include <stdbool.h>
#include <stdint.h>

#include "secded_enc.h"

// Calculates even parity for a 64-bit word
static uint8_t calc_parity(uint64_t word) {
  bool parity = false;

  while (word) {
    if (word & 1) {
      parity = !parity;
    }

    word >>= 1;
  }

  return parity;
}
"""

C_H_TOP = """
#ifndef OPENTITAN_HW_IP_PRIM_DV_PRIM_SECDED_SECDED_ENC_H_
#define OPENTITAN_HW_IP_PRIM_DV_PRIM_SECDED_SECDED_ENC_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

// Integrity encode functions for varying bit widths matching the functionality
// of the RTL modules of the same name. Each takes an array of bytes in
// little-endian order and returns the calculated integrity bits.

"""

C_H_FOOT = """
#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_HW_IP_PRIM_DV_PRIM_SECDED_SECDED_ENC_H_
"""

CODE_OPTIONS = {'hsiao': '', 'hamming': '_hamming'}
PRINT_OPTIONS = {"logic": "assign ", "function": "  "}

# secded configurations
SECDED_CFG_FILE = "util/design/data/secded_cfg.hjson"

# The seed we use to initialise the PRNG when running the randomised algorithm
# to choose constants for Hsiao codes.
_RND_SEED = 123


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


def print_secded_enum_and_util_fns(cfgs):
    enum_vals = ["    SecdedNone"]
    parity_width_vals = []
    data_width_vals = []
    for cfg in cfgs:
        k = cfg['k']
        m = cfg['m']
        n = k + m
        suffix = CODE_OPTIONS[cfg['code_type']]
        formatted_suffix = suffix.replace('_', '').capitalize()

        enum_name = "    Secded%s_%s_%s" % (formatted_suffix, n, k)
        enum_vals.append(enum_name)

        parity_width = "  %s: return %s;" % (enum_name, m)
        parity_width_vals.append(parity_width)

        data_width = "  %s: return %s;" % (enum_name, k)
        data_width_vals.append(data_width)

    enum_str = ",\n".join(enum_vals)
    parity_width_fn_str = "\n".join(parity_width_vals)
    data_width_fn_str = "\n".join(data_width_vals)

    enum_str = '''
  typedef enum int {{
{}
  }} prim_secded_e;

  function automatic int get_ecc_data_width(prim_secded_e ecc_type);
    case (ecc_type)
{}
      // Return a non-zero width to avoid VCS compile issues
      default: return 32;
    endcase
  endfunction

  function automatic int get_ecc_parity_width(prim_secded_e ecc_type);
    case (ecc_type)
{}
      default: return 0;
    endcase
  endfunction
'''.format(enum_str, data_width_fn_str, parity_width_fn_str)

    return enum_str


def print_pkg_types(n, k, m, codes, suffix, codetype):
    typename = "secded%s_%d_%d_t" % (suffix, n, k)

    typestr = '''
  typedef struct packed {{
    logic [{}:0] data;
    logic [{}:0] syndrome;
    logic [1:0]  err;
  }} {};
'''.format((k - 1), (m - 1), typename)

    return typestr


def print_fn(n, k, m, codes, suffix, codetype):
    enc_out = print_enc(n, k, m, codes)
    dec_out = print_dec(n, k, m, codes, codetype, "function")

    typename = "secded_%d_%d_t" % (n, k)
    module_name = "prim_secded%s_%d_%d" % (suffix, n, k)

    outstr = '''
  function automatic logic [{}:0] {}_enc (logic [{}:0] data_i);
    logic [{}:0] data_o;
{}    return data_o;
  endfunction

  function automatic {} {}_dec (logic [{}:0] data_i);
    logic [{}:0] data_o;
    logic [{}:0] syndrome_o;
    logic [1:0]  err_o;

    {} dec;

{}
    dec.data      = data_o;
    dec.syndrome  = syndrome_o;
    dec.err       = err_o;
    return dec;

  endfunction
'''.format((n - 1), module_name, (k - 1), (n - 1), enc_out,
           typename, module_name, (n - 1), (k - 1), (m - 1), typename, dec_out)

    return outstr


def print_enc(n, k, m, codes):
    outstr = "    data_o = {}'(data_i);\n".format(n)
    format_str = "    data_o[{}] = ^(data_o & " + str(n) + "'h{:0" + str(
        (n + 3) // 4) + "X});\n"
    # Print parity computation
    for j, mask in enumerate(calc_bitmasks(k, m, codes, False)):
        outstr += format_str.format(j + k, mask)
    return outstr


def calc_syndrome(code):
    log.info("in syndrome {}".format(code))
    return sum(map((lambda x: 2**x), code))


def print_dec(n, k, m, codes, codetype, print_type="logic"):

    preamble = PRINT_OPTIONS[print_type]

    outstr = ""
    if codetype == "hsiao":
        outstr += "  {}logic single_error;\n".format(
            preamble if print_type == "function" else "")

    outstr += "\n"
    outstr += "  {}// Syndrome calculation\n".format(
        preamble if print_type == "function" else "")
    format_str = "  {}".format(preamble) + "syndrome_o[{}] = ^(data_i & " \
        + str(n) + "'h{:0" + str((n + 3) // 4) + "X});\n"

    # Print syndrome computation
    for j, mask in enumerate(calc_bitmasks(k, m, codes, True)):
        outstr += format_str.format(j, mask)
    outstr += "\n"
    outstr += "  {}// Corrected output calculation\n".format(
        preamble if print_type == "function" else "")
    for i in range(k):
        outstr += "  {}".format(preamble)
        outstr += "data_o[%d] = (syndrome_o == %d'h%x) ^ data_i[%d];\n" % (
            i, m, calc_syndrome(codes[i]), i)
    outstr += "\n"
    outstr += "  {}// err_o calc. bit0: single error, bit1: double error\n".format(
        preamble if print_type == "function" else "")
    # The Hsiao and Hamming syndromes are interpreted slightly differently.
    if codetype == "hamming":
        outstr += "  {}".format(preamble) + "err_o[0] = syndrome_o[%d];\n" % (m - 1)
        outstr += "  {}".format(preamble) + "err_o[1] = |syndrome_o[%d:0] & ~syndrome_o[%d];\n" % (
            m - 2, m - 1)
    else:
        outstr += "  {}".format(preamble) + "single_error = ^syndrome_o;\n"
        outstr += "  {}".format(preamble) + "err_o[0] = single_error;\n"
        outstr += "  {}".format(preamble) + "err_o[1] = ~single_error & (|syndrome_o);\n"
    return outstr


# return whether an integer is a power of 2
def is_pow2(n):
    return (n & (n - 1) == 0) and n != 0


def is_odd(n):
    return (n % 2) > 0


def verify(cfgs):
    error = 0
    for cfg in cfgs['cfgs']:
        if (cfg['k'] <= 1 or cfg['k'] > 120):
            error += 1
            log.error("Current tool doesn't support the value k (%d)", cfg['k'])

        if (cfg['m'] <= 1 or cfg['m'] > 20):
            error += 1
            log.error("Current tool doesn't support the value m (%d)", cfg['m'])

        # Calculate 'm' (parity size)
        min_m = min_paritysize(cfg['k'])
        if (cfg['m'] < min_m):
            error += 1
            log.error("given \'m\' argument is smaller than minimum requirement " +
                      "using calculated minimum (%d)", min_m)

        # Error check code selection
        if (cfg['code_type'] not in CODE_OPTIONS):
            error += 1
            log.error("Invalid code {} selected, use one of {}".format(
                cfg['code_type'], CODE_OPTIONS))

    return error


def gen_code(codetype, k, m):
    # The hsiao_code generator uses (pseudo)random values to pick good ECC
    # constants. Rather than exposing the seed, we pick a fixed one here to
    # ensure everything stays stable in future.
    old_rnd_state = random.getstate()
    random.seed(_RND_SEED)
    try:
        return globals()["_{}_code".format(codetype)](k, m)
    finally:
        random.setstate(old_rnd_state)


def generate(cfgs, args):
    pkg_out_str = ""
    pkg_type_str = ""

    c_src_filename = args.c_outdir + "/" + "secded_enc.c"
    c_h_filename = args.c_outdir + "/" + "secded_enc.h"

    with open(c_src_filename, "w") as f:
        f.write(COPYRIGHT)
        f.write("// SECDED encode code generated by\n")
        f.write(f"// util/design/secded_gen.py from {SECDED_CFG_FILE}\n\n")
        f.write(C_SRC_TOP)

    with open(c_h_filename, "w") as f:
        f.write(COPYRIGHT)
        f.write("// SECDED encode code generated by\n")
        f.write(f"// util/design/secded_gen.py from {SECDED_CFG_FILE}\n")
        f.write(C_H_TOP)

    for cfg in cfgs['cfgs']:
        log.debug("Working on {}".format(cfg))
        k = cfg['k']
        m = cfg['m']
        n = k + m
        codetype = cfg['code_type']
        suffix = CODE_OPTIONS[codetype]
        codes = gen_code(codetype, k, m)

        # write out rtl files
        write_enc_dec_files(n, k, m, codes, suffix, args.outdir, codetype)

        # write out C files, only hsiao codes are supported
        if codetype == "hsiao":
            write_c_files(n, k, m, codes, suffix, c_src_filename, c_h_filename)

        # write out package typedefs
        pkg_type_str += print_pkg_types(n, k, m, codes, suffix, codetype)
        # print out functions
        pkg_out_str += print_fn(n, k, m, codes, suffix, codetype)

        if not args.no_fpv:
            write_fpv_files(n, k, m, codes, suffix, args.fpv_outdir)

    with open(c_h_filename, "a") as f:
        f.write(C_H_FOOT)

    format_c_files(c_src_filename, c_h_filename)

    # create enum of various ECC types - useful for DV purposes in mem_bkdr_if
    enum_str = print_secded_enum_and_util_fns(cfgs['cfgs'])
    # write out package file
    full_pkg_str = enum_str + pkg_type_str + pkg_out_str
    write_pkg_file(args.outdir, full_pkg_str)


# k = data bits
# m = parity bits
# generate hsiao code
def _hsiao_code(k, m):
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
def _hamming_code(k, m):

    n = k + m

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


def write_pkg_file(outdir, pkg_str):
    with open(outdir + "/" + "prim_secded_pkg.sv", "w") as f:
        outstr = '''{}// SECDED package generated by
// util/design/secded_gen.py from {}

package prim_secded_pkg;
{}

endpackage
'''.format(COPYRIGHT, SECDED_CFG_FILE, pkg_str)
        f.write(outstr)


def bytes_to_c_type(num_bytes):
    if num_bytes == 1:
        return 'uint8_t'
    elif num_bytes <= 2:
        return 'uint16_t'
    elif num_bytes <= 4:
        return 'uint32_t'
    elif num_bytes <= 8:
        return 'uint64_t'

    return None


def write_c_files(n, k, m, codes, suffix, c_src_filename, c_h_filename):
    in_bytes = math.ceil(k / 8)
    out_bytes = math.ceil(m / 8)

    if (k > 64):
        log.warning(f"Cannot generate C encoder for k = {k}."
                    " The tool has no support for k > 64 for C encoder "
                    "generation")
        return

    in_type = bytes_to_c_type(in_bytes)
    out_type = bytes_to_c_type(out_bytes)

    assert in_type
    assert out_type

    with open(c_src_filename, "a") as f:
        # Write out function prototype in src
        f.write(f"\n{out_type} enc_secded_{n}_{k}{suffix}"
                f"(const uint8_t bytes[{in_bytes}]) {{\n")

        # Form a single word from the incoming byte data
        f.write(f"{in_type} word = ")
        f.write(" | ".join(
                [f"(({in_type})bytes[{i}] << {i*8})" for i in range(in_bytes)]))
        f.write(";\n\n")

        # AND the word with the codes, calculating parity of each and combine
        # into a single word of integrity bits
        f.write("return ")
        parity_bit_masks = enumerate(calc_bitmasks(k, m, codes, False))
        f.write(" | ".join(
                [f"(calc_parity(word & 0x{mask:x}) << {par_bit})" for par_bit,
                    mask in parity_bit_masks]))

        f.write(";\n}\n")

    with open(c_h_filename, "a") as f:
        # Write out function declaration in header
        f.write(f"{out_type} enc_secded_{n}_{k}{suffix}"
                f"(const uint8_t bytes[{in_bytes}]);\n")


def format_c_files(c_src_filename, c_h_filename):
    try:
        # Call clang-format to in-place format generated C code. If there are
        # any issues log a warning.
        result = subprocess.run(['clang-format', '-i', c_src_filename,
                                c_h_filename], stderr=subprocess.PIPE,
                                universal_newlines=True)
        result.check_returncode()
    except Exception as e:
        stderr = ''
        if result:
            stderr = '\n' + result.stderr

        log.warning(f"Could not format generated C source: {e}{stderr}")


def write_enc_dec_files(n, k, m, codes, suffix, outdir, codetype):
    enc_out = print_enc(n, k, m, codes)

    module_name = "prim_secded%s_%d_%d" % (suffix, n, k)

    with open(outdir + "/" + module_name + "_enc.sv", "w") as f:
        outstr = '''{}// SECDED encoder generated by util/design/secded_gen.py

module {}_enc (
  input        [{}:0] data_i,
  output logic [{}:0] data_o
);

  always_comb begin : p_encode
{}  end

endmodule : {}_enc
'''.format(COPYRIGHT, module_name, (k - 1), (n - 1), enc_out, module_name)
        f.write(outstr)

    dec_out = print_dec(n, k, m, codes, codetype)

    with open(outdir + "/" + module_name + "_dec.sv", "w") as f:
        outstr = '''{}// SECDED decoder generated by util/design/secded_gen.py

module {}_dec (
  input        [{}:0] data_i,
  output logic [{}:0] data_o,
  output logic [{}:0] syndrome_o,
  output logic [1:0] err_o
);

{}
endmodule : {}_dec
'''.format(COPYRIGHT, module_name, (n - 1), (k - 1), (m - 1),
           dec_out, module_name)
        f.write(outstr)


def write_fpv_files(n, k, m, codes, suffix, outdir):
    module_name = "prim_secded%s_%d_%d" % (suffix, n, k)

    with open(outdir + "/tb/" + module_name + "_fpv.sv", "w") as f:
        outstr = '''{}// SECDED FPV testbench generated by util/design/secded_gen.py

module {}_fpv (
  input               clk_i,
  input               rst_ni,
  input        [{}:0] data_i,
  output logic [{}:0] data_o,
  output logic [{}:0] syndrome_o,
  output logic [1:0]  err_o,
  input        [{}:0] error_inject_i
);

  logic [{}:0] data_enc;

  {}_enc {}_enc (
    .data_i,
    .data_o(data_enc)
  );

  {}_dec {}_dec (
    .data_i(data_enc ^ error_inject_i),
    .data_o,
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
  input [{}:0] data_i,
  input [{}:0] data_o,
  input [{}:0] syndrome_o,
  input [1:0]  err_o,
  input [{}:0] error_inject_i
);

  // Inject a maximum of two errors simultaneously.
  `ASSUME_FPV(MaxTwoErrors_M, $countones(error_inject_i) <= 2)
  // This bounds the input data state space to make sure the solver converges.
  `ASSUME_FPV(DataLimit_M, $onehot0(data_i) || $onehot0(~data_i))
  // Single bit error detection
  `ASSERT(SingleErrorDetect_A, $countones(error_inject_i) == 1 |-> err_o[0])
  `ASSERT(SingleErrorDetectReverse_A, err_o[0] |-> $countones(error_inject_i) == 1)
  // Double bit error detection
  `ASSERT(DoubleErrorDetect_A, $countones(error_inject_i) == 2 |-> err_o[1])
  `ASSERT(DoubleErrorDetectReverse_A, err_o[1] |-> $countones(error_inject_i) == 2)
  // Single bit error correction (implicitly tests the syndrome output)
  `ASSERT(SingleErrorCorrect_A, $countones(error_inject_i) < 2 |-> data_i == data_o)
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
    .data_i,
    .data_o,
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
    parser.add_argument('--c_outdir',
                        default='hw/ip/prim/dv/prim_secded',
                        help='''
        C output directory. The output files are named secded_enc.c and
        secded_enc.h
        ''')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose')

    args = parser.parse_args()

    if (args.verbose):
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(levelname)s: %(message)s")

    with open(SECDED_CFG_FILE, 'r') as infile:
        config = hjson.load(infile)

    # Error checking
    error = verify(config)
    if (error):
        exit(1)

    # Generate outputs
    generate(config, args)


if __name__ == "__main__":
    main()
