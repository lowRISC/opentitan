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
    parser = argparse.ArgumentParser(prog="reg_alert_handler")
    parser.add_argument('input',
                        nargs='?',
                        metavar='file',
                        type=argparse.FileType('r'),
                        default=sys.stdin,
                        help='input template file')
    parser.add_argument('--n_alerts',
                        type=int,
                        default=4,
                        help='Number of alert sources')
    parser.add_argument('--esc_cnt_dw',
                        type=int,
                        default=32,
                        help='Width of escalation counter')
    parser.add_argument('--accu_cnt_dw',
                        type=int,
                        default=16,
                        help='Width of accumulator')
    parser.add_argument('--async_on',
                        type=str,
                        default="'0",
                        help="""Enables asynchronous signalling between specific
                        alert RX/TX pairs""")
    parser.add_argument('--n_lpg',
                        type=int,
                        default=1,
                        help='Number of LPGs')
    parser.add_argument('--lpg_map',
                        type=str,
                        default="'0",
                        help="""Encodes the alert to LPG mapping""")

    args = parser.parse_args()

    # Determine output: if stdin then stdout if not then ??
    out = StringIO()

    reg_tpl = Template(args.input.read())
    out.write(
        reg_tpl.render(n_alerts=args.n_alerts,
                       esc_cnt_dw=args.esc_cnt_dw,
                       accu_cnt_dw=args.accu_cnt_dw,
                       async_on=args.async_on,
                       n_lpg=args.n_lpg,
                       lpg_map=args.lpg_map,
                       n_classes=4))  # leave this constant for now

    print(out.getvalue())

    out.close()


if __name__ == "__main__":
    main()
