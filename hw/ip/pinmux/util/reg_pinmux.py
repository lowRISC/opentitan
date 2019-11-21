#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Convert mako template to Hjson register description
"""
import argparse
import sys
from io import StringIO

from mako.template import Template


def main():
    parser = argparse.ArgumentParser(prog="reg_pinmux")
    parser.add_argument('input',
                        nargs='?',
                        metavar='file',
                        type=argparse.FileType('r'),
                        default=sys.stdin,
                        help='input template file')
    parser.add_argument('--n_periph_in',
                        type=int,
                        help='Number of peripheral inputs',
                        default = 16)
    parser.add_argument('--n_periph_out',
                        type=int,
                        help='Number of peripheral outputs',
                        default = 16)
    parser.add_argument('--n_mio_pads',
                        type=int,
                        help='Number of muxed IO pads',
                        default = 8)

    args = parser.parse_args()

    # Determine output: if stdin then stdout if not then ??
    out = StringIO()

    reg_tpl = Template(args.input.read())
    out.write(
        reg_tpl.render(n_periph_in=args.n_periph_in,
                       n_periph_out=args.n_periph_out,
                       n_mio_pads=args.n_mio_pads))

    print(out.getvalue())

    out.close()


if __name__ == "__main__":
    main()
