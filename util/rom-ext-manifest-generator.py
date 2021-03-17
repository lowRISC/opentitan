#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
This script generates various descriptions of the ROM_EXT manifest format based
on the `sw/device/silicon_creator/rom_exts/manifest.hjson` machine-readable description of that
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
- `template.h`, from `sw/device/silicon_creator/rom_exts/manifest.h.tpl` which provides field
  size and offset preprocessor definitions for use from C.
"""

import argparse
import subprocess
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

  rom-ext-manifest-generator --output-files=[all | c | rust | format]:
    Type of files to be generated:

    all    - All files listed below
    c      - C header file
    rust   - Rust module file
    format - Format description file (plaintext)

  rom-ext-manifest-generator --verbose:
    Print extra information including resulting field offsets and alignment.
"""


class MemoryOffset(object):
    def __init__(self, name, offset):
        self.name = name
        self.offset = offset

    def offset_name(self):
        return self.name + Name(["offset"])


def generate_defines(fields, verbose=False):
    """ Generates manifest defines.

    This produces two lists of tuples. One with a field name and the
    `MemoryRegion` object, and one with `MemoryOffset` object. Please see the
    description at the top for more information on the differences between these
    objects.
    """
    def print_field_info(name, offset, size, alignment, required_alignment):
        if verbose:
            print("0x{:04x} - 0x{:04x}: {} (alignment: {} reqd: {})".format(
                offset, offset + size, name, alignment, required_alignment))

    def print_offset_info(name, offset, alignment, required_alignment):
        if verbose:
            print("       @ 0x{:04x}: {} (alignment: {} reqd: {})".format(
                offset, name, alignment, required_alignment))

    base_name = Name.from_snake_case("ROM_EXT")

    regions = []
    offsets = []
    current_offset_bytes = 0
    for field in fields:
        required_alignment_bits = field.get("alignment", 32)
        assert required_alignment_bits % 8 == 0
        required_alignment_bytes = required_alignment_bits // 8

        # The 8-byte two-step https://zinascii.com/2014/the-8-byte-two-step.html
        # This ends up aligning `new_offset_bytes` to `required_alignment_bytes`
        # that is greater than or equal to `current_offset_bytes`.
        new_offset_bytes = (current_offset_bytes + required_alignment_bytes - 1) \
            & ~(required_alignment_bytes - 1)

        if new_offset_bytes != current_offset_bytes and verbose:
            print("0x{:04x} - 0x{:04x}: - (realignment) -".format(
                current_offset_bytes, new_offset_bytes))

        current_offset_bytes = new_offset_bytes
        # This works becuase e.g. 6 is `0b0...00110` and ~(6-1) is `0b1..11010`,
        # giving a result of `0b0...010`, or 2.
        current_offset_alignment = current_offset_bytes \
            & ~(current_offset_bytes - 1)

        if field['type'] == "offset":
            offset_name = base_name + Name.from_snake_case(field['name'])
            offset = MemoryOffset(offset_name, current_offset_bytes)
            offsets.append((field['name'], offset))

            print_offset_info(field['name'], current_offset_bytes,
                              current_offset_alignment,
                              required_alignment_bytes)

        else:
            assert field['size'] % 8 == 0
            size_bytes = field['size'] // 8
            if field['type'] == "field":
                region_name = base_name + Name.from_snake_case(field['name'])
                region = MemoryRegion(region_name, current_offset_bytes,
                                      size_bytes)
                regions.append((field['name'], region))

                print_field_info(field['name'], current_offset_bytes,
                                 size_bytes, current_offset_alignment,
                                 required_alignment_bytes)
            elif field['type'] == 'reserved' and verbose:
                print_field_info('- reserved -', current_offset_bytes,
                                 size_bytes, current_offset_alignment, 0)

            current_offset_bytes += size_bytes

    return (regions, offsets)


def generate_cheader(regions, offsets, input_dir, output_dir):
    """Generates C header file.

    This uses the lists of `MemoryRegion` and `MemoryOffset` objects, to
    generate a C header, using a template and placing the output into
    `output_dir`.
    """

    template_path = input_dir / 'manifest.h.tpl'
    output_path = output_dir / 'manifest.h'

    with template_path.open('r') as f:
        template = Template(f.read())

    header = template.render(regions=regions, offsets=offsets)

    with output_path.open('w') as f:
        f.write(header)

    print('C header sucessfuly written to {}.'.format(output_path))


def generate_rust_header(regions, offsets, input_dir, output_dir):
    """Generates Rust module.

    This uses the lists of `MemoryRegion` and `MemoryOffset` objects, to
    generate a Rust module, using a template and placing the output into
    `output_dir`.
    """

    template_path = input_dir / 'manifest.rs.tpl'
    output_path = output_dir / 'manifest.rs'

    with template_path.open('r') as f:
        template = Template(f.read())

    header = template.render(regions=regions, offsets=offsets)

    with output_path.open('w') as f:
        f.write(header)

    print('Rust module sucessfuly written to {}.'.format(output_path))


def generate_format_description(regions, output_dir):
    """Generates Plaintext Format Description.

    This uses the `MemoryRegion` objects to generate a format description using
    the `protocol` tool [1]. This produces an ascii diagram of how the fields of
    a format are laid out.

    [1]: https://github.com/luismartingarcia/protocol
    """

    output_path = output_dir / 'manifest.txt'

    truncate_length = 16  # bytes
    bits_in_byte = 8

    verbose_regions = []
    current_offset = 0  # bytes

    truncation_lines = []
    current_truncation_delta = 0  # bytes

    # We need to re-process this info to re-add reserved regions of the right
    # size, and also to truncate really long fields.
    for name, mem_region in regions:
        new_offset = mem_region.base_addr
        assert new_offset >= current_offset

        # Pad with a reserved field to get to new offset
        if new_offset != current_offset:
            verbose_regions.append("- reserved -:{}".format(
                (new_offset - current_offset) * bits_in_byte))

        current_offset = new_offset

        # Add a (potentially truncated) field
        if mem_region.size_bytes > truncate_length:
            # We only allow truncated regions at 4-byte offsets.
            assert (current_offset % 4 == 0)
            verbose_regions.append("{} ({} bits):{}".format(
                name, mem_region.size_bytes * bits_in_byte,
                truncate_length * bits_in_byte))

            # Save some information so we know where to insert the `~~ break ~~` line.
            data_line = (current_offset - current_truncation_delta) // 4
            truncation_lines.append(data_line)
            current_truncation_delta += mem_region.size_bytes - truncate_length

        else:
            verbose_regions.append("{}:{}".format(
                name, mem_region.size_bytes * bits_in_byte))

        current_offset = new_offset + mem_region.size_bytes

    # Add a field for the image itself:
    verbose_regions.append("code image:{}".format(truncate_length *
                                                  bits_in_byte))
    truncation_lines.append((current_offset - current_truncation_delta) // 4)

    protocol_input = ",".join(verbose_regions)
    protocol_result = subprocess.run(
        ["protocol", "--bits", "32", protocol_input],
        universal_newlines=True,
        capture_output=True)
    protocol_output = protocol_result.stdout

    truncation_mark = "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~  break  ~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
    # The formula here depends on the output of `protocol`. The idea is to
    # replace a line *after* the label with `truncation_mark`, preferrably a
    # line that otherwise would denote the space between adjacent words.
    visual_truncations = [line * 2 + 8 for line in truncation_lines]

    with output_path.open('w') as f:
        for idx, line in enumerate(protocol_output.splitlines(keepends=True)):
            if idx in visual_truncations:
                f.write(truncation_mark)
            else:
                f.write(line)

    print('Format description successfully written to {}.'.format(output_path))


def main():
    ALL_PARTS = ["c", "rust", "format"]

    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        usage=USAGE,
        description=DESC)

    parser.add_argument('-v',
                        '--verbose',
                        action='store_true',
                        default=False,
                        help='Print Extra Information.')

    parser.add_argument('--input-dir',
                        required=True,
                        type=Path,
                        help='Manifest hjson and template directory.')

    parser.add_argument('--output-dir',
                        required=True,
                        type=Path,
                        help='Manifest file output directory.')

    parser.add_argument('--output-files',
                        choices=['all'] + ALL_PARTS,
                        default=[],
                        action='append',
                        help='The type of files to be produced.')

    args = parser.parse_args()

    manifest_hjson_file = args.input_dir / 'manifest.hjson'

    with manifest_hjson_file.open('r') as hjson_file:
        obj = hjson.loads(hjson_file.read())

    if len(args.output_files) == 0:
        args.output_files += ['all']
    if 'all' in args.output_files:
        args.output_files += ALL_PARTS

    regions, offsets = generate_defines(obj['fields'], args.verbose)

    if "c" in args.output_files:
        generate_cheader(regions, offsets, args.input_dir, args.output_dir)

    if "rust" in args.output_files:
        generate_rust_header(regions, offsets, args.input_dir, args.output_dir)

    if "format" in args.output_files:
        generate_format_description(regions, args.output_dir)


if __name__ == '__main__':
    main()
