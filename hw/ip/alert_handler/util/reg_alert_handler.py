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

    # can currently not be overridden with this script
    n_lpg = 1
    lpg_map = ["1'b0"]
    async_on = ["'0"]

    args = parser.parse_args()

    # Determine output: if stdin then stdout if not then ??
    out = StringIO()

    reg_tpl = Template(args.input.read())
    out.write(
        reg_tpl.render(n_alerts=args.n_alerts,
                       esc_cnt_dw=args.esc_cnt_dw,
                       accu_cnt_dw=args.accu_cnt_dw,
                       async_on=async_on,
                       n_lpg=n_lpg,
                       lpg_map=lpg_map,
                       n_classes=4))  # leave this constant for now

    print(out.getvalue())

    out.close()


if __name__ == "__main__":
    main()
