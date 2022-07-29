#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Mako template to Hjson register description
"""
import sys
import argparse
from io import StringIO

from mako.template import Template


def main():
    parser = argparse.ArgumentParser(prog="reg_timer")
    parser.add_argument(
        'input',
        nargs='?',
        metavar='file',
        type=argparse.FileType('r'),
        default=sys.stdin,
        help='input template file')
    parser.add_argument('--harts', '-s', type=int, help='Number of Harts')
    parser.add_argument(
        '--timers',
        '-t',
        type=int,
        default=1,
        help='Number of Timers in a Hart. Maximum up to 32')

    args = parser.parse_args()

    if args.timers > 32:
        raise Exception("OOB TIMERS")
    # Determine output: if stdin then stdout if not then ??
    out = StringIO()

    reg_tpl = Template(args.input.read())
    out.write(reg_tpl.render(harts=args.harts, timers=args.timers).rstrip())

    print(out.getvalue())

    out.close()


if __name__ == "__main__":
    main()
