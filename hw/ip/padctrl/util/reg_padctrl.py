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
    parser = argparse.ArgumentParser(prog="reg_padctrl")
    parser.add_argument('input',
                        nargs='?',
                        metavar='file',
                        type=argparse.FileType('r'),
                        default=sys.stdin,
                        help='input template file')
    parser.add_argument('--n_dio_pads',
                        type=int,
                        help='Number of dedicated IO pads',
                        default = 4)
    parser.add_argument('--n_mio_pads',
                        type=int,
                        help='Number of muxed IO pads',
                        default = 16)
    parser.add_argument('--attr_dw',
                        type=int,
                        help='Pad attribute data width',
                        default = 10)

    args = parser.parse_args()

    # Determine output: if stdin then stdout if not then ??
    out = StringIO()

    reg_tpl = Template(args.input.read())
    out.write(
        reg_tpl.render(n_dio_pads=args.n_dio_pads,
                       n_mio_pads=args.n_mio_pads,
                       attr_dw=args.attr_dw))

    print(out.getvalue())

    out.close()


if __name__ == "__main__":
    main()
