#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""This script generates random seeds and state permutations for LFSRs
and outputs them them as a packed SV logic vectors suitable for use with
prim_lfsr.sv.
"""
import argparse
import random
import textwrap
import logging as log
from math import ceil, log2


SV_INSTRUCTIONS = """
------------------------------------------------
| COPY PASTE THE CODE TEMPLATE BELOW INTO YOUR |
| RTL CODE, INLUDING THE COMMENT IN ORDER TO   |
| EASE AUDITABILITY AND REPRODUCIBILITY.       |
------------------------------------------------
"""


def _as_snake_case_prefix(name):
    """ Convert PascalCase name into snake_case name"""
    outname = ""
    for c in name:
        if c.isupper() and len(outname) > 0:
            outname += '_'
        outname += c.lower()
    return outname + ('_' if name else '')


def _get_random_data_hex_literal(width):
    """ Fetch 'width' random bits and return them as hex literal"""
    width = int(width)
    literal_str = hex(random.getrandbits(width))
    literal_str = str(width) + "'h" + literal_str[2:]
    return literal_str


def _get_random_perm_hex_literal(numel):
    """ Compute a random permutation of 'numel' elements and
    return as packed hex literal"""
    num_elements = int(numel)
    width = int(ceil(log2(num_elements)))
    idx = [x for x in range(num_elements)]
    random.shuffle(idx)
    literal_str = ""
    for k in idx:
        literal_str += format(k, '0' + str(width) + 'b')
    # convert to hex for space efficiency
    literal_str = hex(int(literal_str, 2))
    literal_str = str(width * numel) + "'h" + literal_str[2:]
    return literal_str


def _wrapped_docstring():
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


def main():
    log.basicConfig(level=log.INFO,
                    format="%(asctime)s - %(message)s",
                    datefmt="%Y-%m-%d %H:%M")

    parser = argparse.ArgumentParser(
        prog="gen-lfsre-perm",
        description=_wrapped_docstring(),
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('-w',
                        '--width',
                        type=int,
                        default=32,
                        metavar='<#bitwidth>',
                        help='LFSR width.')
    parser.add_argument('-s',
                        '--seed',
                        type=int,
                        metavar='<seed>',
                        help='Custom seed for RNG.')
    parser.add_argument('-p',
                        '--prefix',
                        type=str,
                        metavar='name',
                        default="",
                        help='Optional prefix to add to '
                             'types and parameters. '
                             'Make sure this is PascalCase.')

    args = parser.parse_args()

    if args.width <= 0:
        log.error("LFSR width must be nonzero")
        exit(1)

    if args.seed is None:
        random.seed()
        args.seed = random.getrandbits(32)

    random.seed(args.seed)

    print(SV_INSTRUCTIONS)

    type_prefix = _as_snake_case_prefix(args.prefix)

    outstr = '''
// These LFSR parameters have been generated with
// $ hw/ip/prim/util/gen-lfsr-seed.py --width {} --seed {} --prefix "{}"
parameter int {}LfsrWidth = {};
typedef logic [{}LfsrWidth-1:0] {}lfsr_seed_t;
typedef logic [{}LfsrWidth-1:0][$clog2({}LfsrWidth)-1:0] {}lfsr_perm_t;
parameter {}lfsr_seed_t RndCnst{}LfsrSeedDefault = {};
parameter {}lfsr_perm_t RndCnst{}LfsrPermDefault =
    {};
'''.format(args.width, args.seed, args.prefix,
           args.prefix, args.width,
           args.prefix, type_prefix,
           args.prefix, args.prefix, type_prefix,
           type_prefix, args.prefix, _get_random_data_hex_literal(args.width),
           type_prefix, args.prefix, _get_random_perm_hex_literal(args.width))

    print(outstr)


if __name__ == "__main__":
    main()
