#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A tool for generating the CSR and WSR documentation (for use in README.md)
# from the yaml files that contain it.

import argparse
import os
import sys
from typing import Dict, List

# Ensure that the OpenTitan utils directory is on sys.path. This will allow us
# to import serialize.parse_helpers.
_OTBN_DIR = os.path.normpath(os.path.join(os.path.dirname(__file__), '../..'))
_OT_DIR = os.path.normpath(os.path.join(_OTBN_DIR, '../../..'))
_OT_UTIL_DIR = os.path.join(_OT_DIR, 'util')
sys.path.append(_OT_UTIL_DIR)
from serialize.parse_helpers import check_keys, check_str, check_int  # noqa: E402

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


def validate_bits(name: str, bits: Dict[str, object]) -> None:
    for idx, doc in bits.items():
        # For the actual bit description, we expect either:
        # - a string for a single bit or a field without values
        # - a dict for a field with values
        if not (isinstance(doc, str) or isinstance(doc, dict)):
            raise ValueError(f'Invalid description format for bit {idx!r} in ISR {name!r}.')

        # If it is a single bit or a field without values, there is nothing more to check.
        # If we have a bit field with values, check it.
        if isinstance(doc, dict):
            doc = check_keys(doc, f'bit field {idx} of ISR {name!r}', ['doc', 'values'], [])
            # Check the description and values format
            check_str(doc['doc'], f'description of bit field {idx} of ISR {name!r}')
            assert isinstance(doc['values'], dict)
            for k, v in doc['values'].items():
                check_int(k, f'value index of ISR {name!r}')
                check_str(v, f'description of value {v} in bit field of ISR {name!r}')


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
        validate_bits(uc_name, isr.bits)

        doc_lines += ['<table>',
                      '  <thead>',
                      '    <tr><th>Bit</th><th>Description</th></tr>',
                      '  </thead>',
                      '  <tbody>']

        bit_lines = []
        for idx, doc in isr.bits.items():
            idx_formatted = idx.replace("-", ":")
            doc_raw = doc["doc"] if isinstance(doc, dict) else doc
            doc_no_newlines = doc_raw.replace("\n", " ").strip()

            bit_lines += ['<tr>']
            if isinstance(doc, str):
                # We have a single bit or a bit field without values
                bit_lines += [f'  <td>{idx_formatted}</td>',
                              '  <td>',
                              f'    {doc_no_newlines}',
                              '  </td>']
            elif isinstance(doc, dict):
                # We have a bit field with values
                line_items = [f'<li>{value}: {desc}</li>' for value, desc in doc['values'].items()]

                bit_lines += [f'  <td>{idx_formatted}</td>',
                              '  <td>',
                              f'    {doc_no_newlines}',
                              '    <p>Values:</p><ul>']
                bit_lines += [f'      {item}' for item in line_items]
                bit_lines += ['    </ul>',
                              '  </td>']
            else:
                raise ValueError(f'Invalid description format for bit {idx!r} in ISR {uc_name!r}.')
            bit_lines += ['</tr>']

        for bit in bit_lines:
            doc_lines.append(' ' * 4 + bit)
        doc_lines += ['  </tbody>', '</table>']

    for line in doc_lines:
        if line == '':
            line = '<br>'
        print(indent + ' ' * 4 + line)

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
