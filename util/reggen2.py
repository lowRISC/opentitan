#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Command-line tool to validate and convert register hjson

"""
import argparse
import logging as log
import os
import re
import sys
from pathlib import Path, PurePath

import hjson
import pkg_resources

import reggen2 as reggen

ToolName = 'reggen'
ToolVersion = 2
SUPPORTED_FORMAT = ['html', 'rtl', 'dv', 'c', 'ct']

config = {
    # Use parameter name as it is unless parameter is set to local
    'unroll': False
}


def main():
    # Arguments
    parser = argparse.ArgumentParser(
        prog=ToolName + 'v' + str(ToolVersion),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description='Parameterized Register Generator')
    parser.add_argument('input',
                        nargs='?',
                        metavar='file',
                        type=argparse.FileType('r'),
                        default=sys.stdin,
                        help='input file in Hjson type')
    parser.add_argument('--format',
                        '-t',
                        type=str,
                        help='''Output format.
                        'html', 'rtl', 'dv', 'c', 'ct' are supported.
                        ''')
    parser.add_argument('--outdir',
                        help='Target directory for generated RTL, '\
                             'tool uses ../rtl if blank.')
    parser.add_argument('--outfile',
                        '-o',
                        type=argparse.FileType('w'),
                        default=sys.stdout,
                        help='Target filename for json, html, gfm.')
    parser.add_argument('--param',
                        '-p',
                        type=str,
                        default='',
                        help='''Change the values of the parameters.
                        Only integer value is supported.

                        Format:
                            ParamA=ValA;ParamB=ValB
                        ''')
    parser.add_argument('--verbose',
                        '-v',
                        action='store_true',
                        help='Verbose and run validate twice')

    args = parser.parse_args()

    if not args.format in SUPPORTED_FORMAT:
        log.error(f"Format {args.format} is not supported by the tool")
        raise SystemExit()

    if args.verbose:
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
        log.info("Verbosity is set to DEBUG mode")
    else:
        log.basicConfig(format="%(levelname)s: %(message)s")

    # Validate the input first
    with args.input:
        try:
            log.info(f"Reading the Hjson file {args.input.name}.")
            src_str = args.input.read()
            obj = hjson.loads(src_str,
                              use_decimal=True,
                              object_pairs_hook=reggen.checking_dict)
        except ValueError:
            raise SystemExit(sys.exc_info()[1])

    params = args.param.split(';')
    if args.param != '' and len(params) != 0:
        log.info("Parameter value is given. Set to unroll register mode")
        log.info(f"  Received parameters: {params}")
        config["unroll"] = True

    log.info("Validating the Hjson object.")
    error = reggen.validate(obj, params=params)
    log.info(hjson.dumps(obj))

    log.info("Building the data structure from the Hjson object.")
    block = reggen.elaborate(obj, unroll=False, params=params)
    log.info(str(block))


if __name__ == '__main__':
    main()
