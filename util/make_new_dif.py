#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# make_new_dif.py is a script for instantiating templates needed to begin
# development on a new DIF.
#
# To instantiate the files for a new IP named my_ip, run the command
# $ util/make_new_dif.py --ip my_ip --peripheral "my peripheral"
# where "my peripheral" is a documentation-friendly name for your peripheral.
# Compare "pwrmgr" and "power manager".
#
# It will instantiate:
# - `sw/device/lib/dif/dif_template.h.tpl` as the DIF Header (into dif_<ip>.h).
# - `doc/project/sw_checklist.md.tpl` as the DIF Checklist (into dif_<ip>.md).
#
# See both templates for more information.
#
# You can also use the `--only=header` or `--only=checklist` to instantiate a
# subset of the templates. This can be passed multiple times, and including
# `--only=all` will instantiate every template.
#
# The produced files will still need some cleaning up before they can be used.

import argparse
from pathlib import Path

from mako.template import Template

# This file is $REPO_TOP/util/make_new_dif.py, so it takes two parent()
# calls to get back to the top.
REPO_TOP = Path(__file__).resolve().parent.parent

ALL_PARTS = ["header", "checklist"]


def main():
    dif_dir = REPO_TOP / 'sw/device/lib/dif'

    parser = argparse.ArgumentParser()
    parser.add_argument('--ip',
                        '-i',
                        required=True,
                        help='the short name of the IP, in snake_case')
    parser.add_argument('--peripheral',
                        '-p',
                        required=True,
                        help='the documentation-friendly name of the IP')
    parser.add_argument(
        '--handle-param',
        '-a',
        default='handle',
        help='an optional name to replace the `handle` parameter name')
    parser.add_argument('--only',
                        choices=['all'] + ALL_PARTS,
                        default=[],
                        action='append',
                        help='only create some files; defaults to all.')
    parser.add_argument('--output',
                        '-o',
                        type=Path,
                        default=dif_dir,
                        help='directory to place the output files into.')
    args = parser.parse_args()


    if len(args.only) == 0:
        args.only += ['all']
    if 'all' in args.only:
        args.only += ALL_PARTS

    ip_snake = args.ip
    ip_camel = ''.join([word.capitalize() for word in args.ip.split('_')])
    ip_upper = ip_snake.upper()
    periph_lower = args.peripheral
    # We just want to set the first character to title case. In particular,
    # .capitalize() does not do the right thing, since it would convert
    # UART to Uart.
    periph_upper = periph_lower[0].upper() + periph_lower[1:]
    handle = args.handle_param

    if len(args.only) > 0:
        args.output.mkdir(exist_ok=True)

    if "header" in args.only:
        header_template_file = args.output / 'dif_template.h.tpl'

        with header_template_file.open('r') as f:
            header_template = Template(f.read())

        header_out_file = dif_dir / 'dif_{}.h'.format(ip_snake)
        with header_out_file.open('w') as f:
            f.write(
                header_template.render(
                    ip_snake=ip_snake,
                    ip_camel=ip_camel,
                    ip_upper=ip_upper,
                    periph_lower=periph_lower,
                    periph_upper=periph_upper,
                    handle=handle,
                ))

        print('DIF header successfully written to {}.'.format(
            str(header_out_file)))

    if "checklist" in args.only:
        checklist_template_file = REPO_TOP / 'doc/project/sw_checklist.md.tpl'

        with checklist_template_file.open('r') as f:
            markdown_template = Template(f.read())

        checklist_out_file = args.output / 'dif_{}.md'.format(ip_snake)
        with checklist_out_file.open('w') as f:
            f.write(
                markdown_template.render(
                    ip_name=ip_snake,
                    dif_name=ip_snake,
                    display_name=periph_upper,
                ))

        print('DIF Checklist successfully written to {}.'.format(
            str(checklist_out_file)))


if __name__ == '__main__':
    main()
