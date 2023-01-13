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
import functools
import itertools
import logging as log
import math
import random
import hjson
import subprocess
from typing import Any, Dict, List, Tuple
from pathlib import Path

COPYRIGHT = """// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
"""

C_SRC_TOP = """
#include "secded_enc.h"

#include <stdbool.h>
#include <stdint.h>

// Calculates even parity for a 64-bit word
static uint8_t calc_parity(uint64_t word, bool invert) {
  bool parity = false;

  while (word) {
    if (word & 1) {
      parity = !parity;
    }

    word >>= 1;
  }

  return parity ^ invert;
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

CODE_OPTIONS = {'hsiao': '',
                'inv_hsiao': '_inv',
                'hamming': '_hamming',
                'inv_hamming': '_inv_hamming'}

# secded configurations
SECDED_CFG_FILE = "util/design/data/secded_cfg.hjson"

PROJ_ROOT = Path(__file__).parent.parent.parent
SECDED_CFG_PATH = Path(PROJ_ROOT) / SECDED_CFG_FILE

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
    return tuple(fanin_masks)


def print_secded_enum_and_util_fns(cfgs):
    enum_vals = ["    SecdedNone"]
    parity_width_vals = []
    data_width_vals = []
    for cfg in cfgs:
        k = cfg['k']
        m = cfg['m']
        n = k + m
        suffix = CODE_OPTIONS[cfg['code_type']]
        suffix = suffix.split('_')
        suffix = [x.capitalize() for x in suffix]
        formatted_suffix = ''.join(suffix)

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


def print_pkg_allzero(n, k, m, codes, suffix, codetype):

    suffix = suffix.split('_')
    suffix = [x.capitalize() for x in suffix]
    suffix = ''.join(suffix)

    invecc = 0
    invcode = 0
    if codetype in ["inv_hsiao", "inv_hamming"]:
        for x in range(m):
            invecc += (x % 2) << x
        invcode = invecc << k
    zerostr = f'''
  parameter logic [{m-1}:0] Secded{suffix}{n}{k}ZeroEcc = {m}'h{invecc:0X};
  parameter logic [{n-1}:0] Secded{suffix}{n}{k}ZeroWord = {n}'h{invcode:0X};
'''
    return zerostr


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


def print_fn(n, k, m, codes, suffix, codetype, inv=False):
    enc_out = print_enc(n, k, m, codes, codetype)
    dec_out = print_dec(n, k, m, codes, codetype, "function")

    typename = "secded%s_%d_%d_t" % (suffix, n, k)
    module_name = "prim_secded%s_%d_%d" % (suffix, n, k)

    outstr = '''
  function automatic logic [{}:0]
      {}_enc (logic [{}:0] data_i);
    logic [{}:0] data_o;
{}    return data_o;
  endfunction

  function automatic {}
      {}_dec (logic [{}:0] data_i);
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


def print_enc(n, k, m, codes, codetype):
    invert = 1 if codetype in ["inv_hsiao", "inv_hamming"] else 0
    outstr = "    data_o = {}'(data_i);\n".format(n)
    hex_format = str(n) + "'h{:0" + str((n + 3) // 4) + "X}"
    format_str = "    data_o[{}] = ^(data_o & " + hex_format + ");\n"
    # Print parity computation If inverted encoding is turned on, we only
    # invert every odd bit so that both all-one and all-zero encodings are not
    # possible. This works for most encodings generated if the fanin is
    # balanced (such as inverted Hsiao codes). However, since there is no
    # guarantee, an FPV assertion is added to prove that all-zero and all-one
    # encodings do not exist if an inverted code is used.
    inv_mask = 0
    for j, mask in enumerate(calc_bitmasks(k, m, codes, False)):
        inv_mask += (j % 2) << j
        outstr += format_str.format(j + k, mask)
    # Selectively invert parity bits as determined above.
    if invert:
        outstr += ("    data_o ^= " + hex_format + ";\n").format(inv_mask << k)
    return outstr


def calc_syndrome(code):
    log.info("in syndrome {}".format(code))
    return sum(map((lambda x: 2**x), code))


def print_dec(n, k, m, codes, codetype, print_type="logic"):
    outstr = ""
    outstr += "    // Syndrome calculation\n"
    hexfmt = str(n) + "'h{:0" + str((n + 3) // 4) + "X}"
    format_str = "    syndrome_o[{}] = ^("
    # Add ECC bit inversion if needed (see print_enc function).
    if codetype in ["inv_hsiao", "inv_hamming"]:
        invval = 0
        for x in range(m):
            invval += (x % 2) << x
        format_str += "(data_i ^ " + hexfmt.format(invval << k) + ")"
    else:
        format_str += "data_i"
    format_str += " & " + hexfmt + ");\n"

    # Print syndrome computation
    for j, mask in enumerate(calc_bitmasks(k, m, codes, True)):
        outstr += format_str.format(j, mask)
    outstr += "\n"
    outstr += "    // Corrected output calculation\n"
    for i in range(k):
        outstr += "    data_o[%d] = (syndrome_o == %d'h%x) ^ data_i[%d];\n" % (
            i, m, calc_syndrome(codes[i]), i)
    outstr += "\n"
    outstr += "    // err_o calc. bit0: single error, bit1: double error\n"
    # The Hsiao and Hamming syndromes are interpreted slightly differently.
    if codetype in ["hamming", "inv_hamming"]:
        outstr += "    err_o[0] = syndrome_o[%d];\n" % (m - 1)
        outstr += "    err_o[1] = |syndrome_o[%d:0] & ~syndrome_o[%d];\n" % (
            m - 2, m - 1)
    else:
        outstr += "    err_o[0] = ^syndrome_o;\n"
        outstr += "    err_o[1] = ~err_o[0] & (|syndrome_o);\n"
    return outstr


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


def _ecc_pick_code(config: Dict[str, Any], codetype: str, k: int) -> Tuple[int, List[int], int]:
    # first check to see if bit width is supported among configuration

    codes = None
    bitmasks = None
    m = None
    for cfg in config['cfgs']:
        if cfg['k'] == k and cfg['code_type'] == codetype:
            m = cfg['m']
            codes = gen_code(codetype, k, m)
            bitmasks = calc_bitmasks(k, m, codes, False)
            invert = 1 if codetype in ['inv_hsiao', 'inv_hamming'] else 0
            return (m, bitmasks, invert)

    # error if k not supported
    raise Exception(f'ECC for length {k} of type {codetype} unsupported')


@functools.lru_cache(maxsize=None)
def _ecc_encode(k: int,
                m: int, bitmasks: List[int], invert: int,
                dataword: int) -> int:
    assert 0 <= dataword < (1 << k)

    # represent supplied dataword as a binary string
    word_bin = format(dataword, '0' + str(k) + 'b')

    codeword = word_bin
    for k, mask in enumerate(bitmasks):
        bit = 0
        log.debug(f'codeword: {codeword}')
        log.debug(f'mask: {hex(mask)}')
        mask = (format(mask, '0' + str(k + m) + 'b'))

        # reverse codeword for index selection
        # This is because the LSB is the farthest entry in the string
        codeword_rev = codeword[::-1]
        for idx, f in enumerate(mask[::-1]):
            if int(f):
                bit ^= int(codeword_rev[idx])

        # Add ECC bit inversion if needed (see print_enc function).
        bit ^= (invert & k % 2)
        codeword = str(bit) + codeword
    return codeword


def ecc_encode(config: Dict[str, Any], codetype: str, k: int, dataword: int) -> Tuple[int, int]:
    log.info(f"Encoding ECC for {hex(dataword)}")

    m, bitmasks, invert = _ecc_pick_code(config, codetype, k)
    codeword = _ecc_encode(k, m, bitmasks, invert, dataword)

    # Debug printouts
    log.debug(f'original hex: {hex(dataword)}')
    log.debug(f'codeword hex: {hex(int(codeword,2))}')
    return int(codeword, 2), m


def ecc_encode_some(config: Dict[str, Any],
                    codetype: str,
                    k: int,
                    datawords: int) -> Tuple[List[int], int]:
    m, bitmasks, invert = _ecc_pick_code(config, codetype, k)
    codewords = [int(_ecc_encode(k, m, bitmasks, invert, w), 2)
                 for w in datawords]
    return codewords, m


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
        if codetype in ["hsiao", "inv_hsiao"]:
            write_c_files(n, k, m, codes, suffix, c_src_filename, c_h_filename,
                          codetype)

        # write out all-zero word values for all codes
        pkg_type_str += print_pkg_allzero(n, k, m, codes, suffix, codetype)
        # write out package typedefs
        pkg_type_str += print_pkg_types(n, k, m, codes, suffix, codetype)
        # print out functions
        pkg_out_str += print_fn(n, k, m, codes, suffix, codetype)

        if not args.no_fpv:
            write_fpv_files(n, k, m, codes, suffix, args.fpv_outdir, codetype)

    with open(c_h_filename, "a") as f:
        f.write(C_H_FOOT)

    format_c_files(c_src_filename, c_h_filename)

    # create enum of various ECC types - useful for DV purposes in mem_bkdr_if
    enum_str = print_secded_enum_and_util_fns(cfgs['cfgs'])
    # write out package file
    full_pkg_str = enum_str + pkg_type_str + pkg_out_str
    write_pkg_file(args.outdir, full_pkg_str)


def _inv_hsiao_code(k, m):
    return _hsiao_code(k, m)


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


def _inv_hamming_code(k, m):
    return _hamming_code(k, m)


# Generate hamming code.
# total_cnt = number of total bits
# data_cnt = number of data bits
# parity_cnt = number of parity bits
@functools.lru_cache(maxsize=None)
def _hamming_code(data_cnt, parity_cnt):
    # construct a list of code tuples.
    # Tuple corresponds to each bit position and shows which parity bit it participates in
    # Only the data bits are shown, the parity bits are not.
    total_cnt = data_cnt + parity_cnt
    last_parity = parity_cnt - 1
    # Data bits.
    # This excludes bit 0, the last bit, and any bit whose index is a power of 2.
    data_bits = [b for b in range(1, total_cnt) if b & (b - 1)]
    # Include the closest previous parity bit if it's odd.
    # Also include the final parity bit since it includes everything.
    codes = [
        tuple(p for p in range(last_parity) if (b >> p) & 1) + (last_parity,) for b in data_bits
    ]
    # Final parity bit includes all ECC bits.
    codes += [(last_parity,)] * last_parity
    log.info("Hamming codes %s", codes)
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


def write_c_files(n, k, m, codes, suffix, c_src_filename, c_h_filename,
                  codetype):
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
    assert codetype in ["hsiao", "inv_hsiao"]
    invert = (codetype == "inv_hsiao")

    with open(c_src_filename, "a") as f:
        # Write out function prototype in src
        f.write(f"\n{out_type} enc_secded{suffix}_{n}_{k}"
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
        # Add ECC bit inversion if needed (see print_enc function).
        f.write(" | ".join(
                [f"(calc_parity(word & 0x{mask:x}, "
                 f"{'true' if invert and (par_bit % 2) else 'false'}) << {par_bit})"
                 for par_bit, mask in parity_bit_masks]))

        f.write(";\n}\n")

    with open(c_h_filename, "a") as f:
        # Write out function declaration in header
        f.write(f"{out_type} enc_secded{suffix}_{n}_{k}"
                f"(const uint8_t bytes[{in_bytes}]);\n")


def format_c_files(c_src_filename, c_h_filename):
    try:
        # Call clang-format to in-place format generated C code. If there are
        # any issues log a warning.
        result = subprocess.run(['./ci/bazelisk.sh', 'run', '//quality:clang_format_fix', '--',
                                c_src_filename, c_h_filename], stderr=subprocess.PIPE,
                                universal_newlines=True)
        result.check_returncode()
    except Exception as e:
        stderr = ''
        if result:
            stderr = '\n' + result.stderr

        log.warning(f"Could not format generated C source: {e}{stderr}")


def write_enc_dec_files(n, k, m, codes, suffix, outdir, codetype):
    enc_out = print_enc(n, k, m, codes, codetype)

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

  always_comb begin : p_encode
{}  end
endmodule : {}_dec
'''.format(COPYRIGHT, module_name, (n - 1), (k - 1), (m - 1),
           dec_out, module_name)
        f.write(outstr)


def write_fpv_files(n, k, m, codes, suffix, outdir, codetype):
    module_name = "prim_secded%s_%d_%d" % (suffix, n, k)

    with open(outdir + "/tb/" + module_name + "_tb.sv", "w") as f:
        outstr = '''{}// SECDED FPV testbench generated by util/design/secded_gen.py

module {}_tb (
  input               clk_i,
  input               rst_ni,
  input        [{}:0] data_i,
  output logic [{}:0] data_o,
  output logic [{}:0] encoded_o,
  output logic [{}:0] syndrome_o,
  output logic [1:0]  err_o,
  input        [{}:0] error_inject_i
);

  {}_enc {}_enc (
    .data_i,
    .data_o(encoded_o)
  );

  {}_dec {}_dec (
    .data_i(encoded_o ^ error_inject_i),
    .data_o,
    .syndrome_o,
    .err_o
  );

endmodule : {}_tb
'''.format(COPYRIGHT, module_name, (k - 1), (k - 1), (n - 1), (m - 1), (n - 1),
           module_name, module_name, module_name, module_name, module_name)
        f.write(outstr)

    # Additional assertions for inverted codes.
    if codetype in ["inv_hsiao", "inv_hamming"]:
        inv_asserts = '''
  // Check that all-one and all-zero data does not result in all-one or all-zero codewords
  `ASSERT(AllZerosCheck_A, data_i == '0 |-> encoded_o != '0)
  `ASSERT(AllOnesCheck_A, data_i == '1 |-> encoded_o != '1)

'''
    else:
        inv_asserts = ""

    with open(outdir + "/vip/" + module_name + "_assert_fpv.sv", "w") as f:
        outstr = '''{}// SECDED FPV assertion file generated by util/design/secded_gen.py

module {}_assert_fpv (
  input        clk_i,
  input        rst_ni,
  input [{}:0] data_i,
  input [{}:0] data_o,
  input [{}:0] encoded_o,
  input [{}:0] syndrome_o,
  input [1:0]  err_o,
  input [{}:0] error_inject_i
);

  // Inject a maximum of two errors simultaneously.
  `ASSUME_FPV(MaxTwoErrors_M, $countones(error_inject_i) <= 2)
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
{}
endmodule : {}_assert_fpv
'''.format(COPYRIGHT, module_name, (k - 1), (k - 1), (n - 1), (m - 1), (n - 1),
           inv_asserts, module_name)
        f.write(outstr)

    with open(outdir + "/tb/" + module_name + "_bind_fpv.sv", "w") as f:
        outstr = '''{}// SECDED FPV bind file generated by util/design/secded_gen.py

module {}_bind_fpv;

  bind {}_tb
    {}_assert_fpv {}_assert_fpv (
    .clk_i,
    .rst_ni,
    .data_i,
    .data_o,
    .encoded_o,
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
      - tb/{}_tb.sv
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
      - {}_tb

  formal:
    <<: *default_target

  lint:
    <<: *default_target

'''.format(module_name, module_name, module_name, module_name, module_name)
        f.write(outstr)


def load_secded_config() -> Dict[str, Any]:
    return hjson.load(SECDED_CFG_PATH.open())


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
