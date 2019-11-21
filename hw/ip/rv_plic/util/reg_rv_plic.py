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
    parser = argparse.ArgumentParser(prog="reg_rv_plic")
    parser.add_argument('input',
                        nargs='?',
                        metavar='file',
                        type=argparse.FileType('r'),
                        default=sys.stdin,
                        help='input template file')
    parser.add_argument('--sources',
                        '-s',
                        type=int,
                        help='Number of Interrupt Sources')
    parser.add_argument('--targets',
                        '-t',
                        type=int,
                        default=1,
                        help='Number of Interrupt Targets')
    parser.add_argument('--priority',
                        '-p',
                        type=int,
                        default=7,
                        help='Max value of interrupt priorities')

    args = parser.parse_args()

    # Determine output: if stdin then stdout if not then ??
    out = StringIO()

    reg_tpl = Template(args.input.read())
    out.write(
        reg_tpl.render(src=args.sources,
                       target=args.targets,
                       prio=args.priority))

    print(out.getvalue())

    out.close()


if __name__ == "__main__":
    main()
