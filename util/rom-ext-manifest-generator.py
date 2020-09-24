#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
from pathlib import Path

import hjson
from mako.template import Template

from topgen.c import MemoryRegion, Name

DESC = """ROM_EXT manifest generator"""

USAGE = """
  rom-ext-manifest-generator --input-dir:
    Directory where manifest.hjson and manifest.h.tpl reside.

  rom-ext-manifest-generator --output-dir:
    Directory where manifest.hjson and manifest.h.tpl reside.
"""


def generate_cheader(fields, input_dir, output_dir):
    """ Generates C header file from the `template_file`.

    It produces a list of tuples with a field name and the `MemoryRegion`
    object, whic is used in the `template_path`. The resulting header file is
    placed into `output_path`.
    """

    template_path = input_dir / 'manifest.h.tpl'
    output_path = output_dir / 'manifest.h'

    base_name = Name.from_snake_case("ROM_EXT")

    items = []
    offset = 0
    for field in fields:
        assert field['size'] % 8 == 0
        size_bytes = field['size'] // 8
        if field['type'] == "field":
            region_name = base_name + Name.from_snake_case(field['name'])
            region = MemoryRegion(region_name, offset, size_bytes)
            items.append((field['name'], region))
        offset += size_bytes

    with template_path.open('r') as f:
        template = Template(f.read())

    header = template.render(items=items)

    with output_path.open('w') as f:
        f.write(header)

    print('Template sucessfuly written to {}.'.format(output_path))


def main():
    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        usage=USAGE,
        description=DESC)

    parser.add_argument('--input-dir',
                        required=True,
                        type=Path,
                        help='Manifest hjson and template directory.')

    parser.add_argument('--output-dir',
                        required=True,
                        type=Path,
                        help='Manifest header output directory.')

    args = parser.parse_args()

    manifest_hjson_file = args.input_dir / 'manifest.hjson'

    with manifest_hjson_file.open('r') as hjson_file:
        obj = hjson.loads(hjson_file.read())

    generate_cheader(obj['fields'], args.input_dir, args.output_dir)


if __name__ == '__main__':
    main()
