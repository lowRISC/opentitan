#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A tool for generating the CSR and WSR documentation (for use in README.md)
# from the yaml files that contain it.

import argparse
import os
import sys
from typing import List

sys.path.append(os.path.normpath(os.path.join(os.path.dirname(__file__),
                                              '../../util')))

from shared.isr import Isr, read_isrs  # noqa: E402


def print_thead(indent: str, columns: List[str]) -> None:
    print(f'{indent}<thead>')
    print(f'{indent}  <tr>')
    for column in columns:
        print(f'{indent}    <th>{column}</th>')
    print(f'{indent}  </tr>')
    print(f'{indent}</thead>')


def print_isr(indent: str, isr: Isr, add_anchors: bool) -> None:
    uc_name = isr.name.upper()
    lc_key = isr.name.lower().replace('_', '-')

    print(f'{indent}<tr>')
    print(f'{indent}  <td>0x{isr.address:X}</td>')
    print(f'{indent}  <td>{isr.access_str()}</td>')
    if add_anchors:
        print(f'{indent}  <td><a name="{lc_key}">{uc_name}</a></td>')
    else:
        print(f'{indent}  <td>{uc_name}</td>')
    print(f'{indent}  <td>')

    doc_lines = isr.doc.splitlines()
    if isr.bits:
        doc_lines += ['<table>',
                      '  <thead>',
                      '    <tr><th>Bit</th><th>Description</th></tr>',
                      '  </thead>',
                      '  <tbody>']
        for k, v in isr.bits.items():
            doc_lines.append(f'    <tr><td>{k}</td><td>{v}</td></tr>')
        doc_lines += ['  </tbody>', '</table>']

    for line in doc_lines:
        if line:
            line = indent + ' ' * 4 + line
        print(line)

    print(f'{indent}  </td>')
    print(f'{indent}</tr>')


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--add-anchors', action='store_true')
    parser.add_argument('yml')

    args = parser.parse_args()

    print('<table>')
    print_thead(' ' * 2, ['Number', 'Access', 'Name', 'Description'])
    print('  <tbody>')
    for isr in read_isrs(args.yml):
        print_isr('  ' * 2, isr, args.add_anchors)

    print('  </tbody>')
    print('</table>')


if __name__ == '__main__':
    main()
