#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# make_new_dif.py is a script for quickly applying replacement operations to
# dif_template.h.tpl. See sw/device/lib/dif/dif_template.h.tpl for more
# information.
#
# The produced file may still require spell-checking and general cleaning-up.

import argparse

from pathlib import Path

from mako.template import Template

# This file is $REPO_TOP/util/make_new_dif.py, so it takes two parent()
# calls to get back to the top.
REPO_TOP = Path(__file__).resolve().parent.parent


def main():
    dif_dir = REPO_TOP / 'sw/device/lib/dif'
    template_file = dif_dir / 'dif_template.h.tpl'

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
        help='an optional name to replace the `handle` perameter name')
    parser.add_argument('--template',
                        '-t',
                        type=Path,
                        default=template_file,
                        help='where to find the header template')
    parser.add_argument('--output',
                        '-o',
                        type=Path,
                        help='where to write the header; defaults to dif_ip.h')
    args = parser.parse_args()

    ip_snake = args.ip
    ip_camel = ''.join([word.capitalize() for word in args.ip.split('_')])
    ip_upper = ip_snake.upper()
    periph_lower = args.peripheral
    # We just want to set the first character to title case. In particular,
    # .capitalize() does not do the right thing, since it would convert
    # UART to Uart.
    periph_upper = periph_lower[0].upper() + periph_lower[1:]
    handle = args.handle_param

    with args.template.open('r') as f:
        template = Template(f.read())

    header = template.render(
        ip_snake=ip_snake,
        ip_camel=ip_camel,
        ip_upper=ip_upper,
        periph_lower=periph_lower,
        periph_upper=periph_upper,
        handle=handle,
    )

    dif_file = args.output or dif_dir / 'dif_{}.h'.format(ip_snake)
    with dif_file.open('w') as f:
        f.write(header)
    print('Template sucessfuly written to {}.'.format(str(dif_file)))


if __name__ == '__main__':
    main()
