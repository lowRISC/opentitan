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
    parser.add_argument('--n_mio_periph_in',
                        type=int,
                        help='Number of muxed peripheral inputs',
                        default=33)
    parser.add_argument('--n_mio_periph_out',
                        type=int,
                        help='Number of muxed peripheral outputs',
                        default=32)
    parser.add_argument('--n_mio_pads',
                        type=int,
                        help='Number of muxed IO pads',
                        default=32)
    parser.add_argument('--n_dio_periph_in',
                        type=int,
                        help='Number of dedicated peripheral inputs',
                        default=16)
    parser.add_argument('--n_dio_periph_out',
                        type=int,
                        help='Number of dedicated peripheral outputs',
                        default=16)
    parser.add_argument('--n_dio_pads',
                        type=int,
                        help='Number of dedicated IO pads',
                        default=16)
    parser.add_argument('--n_wkup_detect',
                        type=int,
                        help='Number of wakeup condition detectors',
                        default=8)
    parser.add_argument('--wkup_cnt_width',
                        type=int,
                        help='With of wakeup counters',
                        default=8)
    parser.add_argument('--attr_dw',
                        type=int,
                        help='Pad attribute data width',
                        default = 10)


    args = parser.parse_args()

    # Determine output: if stdin then stdout if not then ??
    out = StringIO()

    reg_tpl = Template(args.input.read())
    out.write(
        reg_tpl.render(n_mio_periph_in=args.n_mio_periph_in,
                       n_mio_periph_out=args.n_mio_periph_out,
                       n_mio_pads=args.n_mio_pads,
                       n_dio_periph_in=args.n_dio_periph_in,
                       n_dio_periph_out=args.n_dio_periph_out,
                       n_dio_pads=args.n_dio_pads,
                       n_wkup_detect=args.n_wkup_detect,
                       wkup_cnt_width=args.wkup_cnt_width,
                       attr_dw=args.attr_dw,
                       usb_start_pos=0,
                       n_usb_pins=0,
                       usb_dp_sel=0,
                       usb_dn_sel=0,
                       usb_dp_pull_sel=0,
                       usb_dn_pull_sel=0))

    print(out.getvalue())

    out.close()


if __name__ == "__main__":
    main()
