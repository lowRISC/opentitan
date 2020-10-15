#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
This script generates various descriptions of the ROM_EXT manifest format based
on the `sw/device/rom_exts/manifest.hjson` machine-readable description of that
format.

The main part of `mainfest.hjson` is a list of fields described using a list of
dicts. These features are given in sequential order.

Each dict can describe one of the following kinds of data format features:
- `type: reserved` which is a reserved area of a certain size. These definitions
  are not named, and definitions are not produced for them.
- `type: field` which is a readable field of a certain size. We generate
  definitions for the start offset of the field, and for the field size (in both
  bytes and words). These must have a name.
- `type: offset` which is a named offset into the ROM_EXT image. This implicitly
  has a size of zero, but no size definitions are given for these fields.
  Offsets with an alignment can move any features that follow them. These must
  have a name.

All data format features have a default alignment of 32-bits. This alignment can
be reduced or expanded with the `alignment` key.

All sizes and alignments are given in *bits*, not bytes.

All fields and offsets must have a name, and optionally a description in the
`desc` key.

The generator currently produces the following files (into the given output
directory):
- `template.h`, from `sw/device/rom_exts/manifest.h.tpl` which provides field
  size and offset preprocessor definitions for use from C.
"""

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
    Directory where manifest.h will be created.
"""

class MemoryOffset(object):
    def __init__(self, name, offset):
        self.name = name
        self.offset = offset

    def offset_name(self):
        return self.name + Name(["offset"])


def generate_cheader(fields, input_dir, output_dir):
    """ Generates C header file from the `template_file`.

    It produces a list of tuples with a field name and the `MemoryRegion`
    object, which is used in the `template_path`. The resulting header file is
    placed into `output_path`.
    """

    template_path = input_dir / 'manifest.h.tpl'
    output_path = output_dir / 'manifest.h'

    base_name = Name.from_snake_case("ROM_EXT")

    regions = []
    offsets = []
    current_offset_bytes = 0
    for field in fields:
        required_alignment_bits = field.get("alignment", 32)
        assert required_alignment_bits % 8 == 0
        required_alignment_bytes = required_alignment_bits // 8

        # The 8-byte two-step https://zinascii.com/2014/the-8-byte-two-step.html
        # This ends up aligning `current_offset_bytes` to `required_alignment_bytes`
        # that is greater than or equal to `current_offset_bytes`.
        current_offset_bytes = (current_offset_bytes + required_alignment_bytes - 1) \
                             & ~(required_alignment_bytes - 1)

        if field['type'] == "offset":
            offset_name = base_name + Name.from_snake_case(field['name'])
            offset = MemoryOffset(offset_name, current_offset_bytes)
            offsets.append((field['name'], offset))

        else:
            assert field['size'] % 8 == 0
            size_bytes = field['size'] // 8
            if field['type'] == "field":
                region_name = base_name + Name.from_snake_case(field['name'])
                region = MemoryRegion(region_name, current_offset_bytes, size_bytes)
                regions.append((field['name'], region))
            current_offset_bytes += size_bytes

    with template_path.open('r') as f:
        template = Template(f.read())

    header = template.render(regions=regions, offsets=offsets)

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
