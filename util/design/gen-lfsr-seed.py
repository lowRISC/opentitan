#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""This script generates random seeds and state permutations for LFSRs
and outputs them them as a packed SV logic vectors suitable for use with
prim_lfsr.sv.
"""
import argparse
import logging as log
import random

from lib import common as common

SV_INSTRUCTIONS = """
------------------------------------------------
| COPY PASTE THE CODE TEMPLATE BELOW INTO YOUR |
| RTL CODE, INLUDING THE COMMENT IN ORDER TO   |
| EASE AUDITABILITY AND REPRODUCIBILITY.       |
------------------------------------------------
"""


def main():
    log.basicConfig(level=log.INFO,
                    format="%(levelname)s: %(message)s")

    parser = argparse.ArgumentParser(
        prog="gen-lfsre-perm",
        description=common.wrapped_docstring(),
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

    type_prefix = common.as_snake_case_prefix(args.prefix)

    outstr = '''
// These LFSR parameters have been generated with
// $ ./util/design/gen-lfsr-seed.py --width {} --seed {} --prefix "{}"
parameter int {}LfsrWidth = {};
typedef logic [{}LfsrWidth-1:0] {}lfsr_seed_t;
typedef logic [{}LfsrWidth-1:0][$clog2({}LfsrWidth)-1:0] {}lfsr_perm_t;
parameter {}lfsr_seed_t RndCnst{}LfsrSeedDefault = {{
  {}
}};
parameter {}lfsr_perm_t RndCnst{}LfsrPermDefault = {{
  {}
}};
'''.format(args.width, args.seed, args.prefix, args.prefix, args.width,
           args.prefix, type_prefix, args.prefix, args.prefix, type_prefix,
           type_prefix, args.prefix,
           common.get_random_data_hex_literal(args.width), type_prefix,
           args.prefix, common.get_random_perm_hex_literal(args.width))

    print(outstr)


if __name__ == "__main__":
    main()
