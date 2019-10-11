#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Command-line tool to parse and process testplan hjson

"""
import argparse
import logging as log
import os
import sys
from pathlib import PurePath

import hjson

from testplanner import testplan_utils


def main():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        'testplan',
        metavar='<hjson-file>',
        help='input testplan file in hjson')
    parser.add_argument(
        '-r',
        '--regr_results',
        metavar='<hjson-file>',
        help='input regression results file in hjson')
    parser.add_argument(
        '--outfile',
        '-o',
        type=argparse.FileType('w'),
        default=sys.stdout,
        help='output html file (without css)')
    args = parser.parse_args()
    outfile = args.outfile

    with outfile:
        testplan_utils.gen_html(args.testplan, args.regr_results, outfile)


if __name__ == '__main__':
    main()
