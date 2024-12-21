#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Top Module Generator
"""
import argparse
import logging as log
import sys

from reggen.ip_block import IpBlock
from raclgen.lib import parse_racl_config, parse_racl_mapping

DESC = """raclgen, generate RACL selection vectors for a given IP"""


def main():
    parser = argparse.ArgumentParser(
        prog="raclgen",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=DESC)
    parser.add_argument('racl_mapping',
                        nargs='?',
                        metavar='file',
                        type=argparse.FileType('r'),
                        help='input file in Hjson type')
    parser.add_argument('-r',
                        '--racl_config',
                        metavar='file',
                        type=argparse.FileType('r'),
                        help='RACL configuration')
    parser.add_argument('-i',
                        '--ip_config',
                        metavar='file',
                        type=argparse.FileType('r'),
                        help='IP configuration')
    parser.add_argument('-f',
                        '--interface',
                        action='store_const',
                        help='Register interface')
    args = parser.parse_args()

    verbose = args.verbose
    if verbose:
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(levelname)s: %(message)s")

    # Read the top-level RACL information
    racl_config = parse_racl_config(args.racl_config)
    ip_config = IpBlock.from_path(args.ip_config)
    racl_mapping = parse_racl_mapping(racl_config, args.racl_mapping_path, args.interface, 
                                      ip_config)


if __name__ == '__main__':
    sys.exit(main())