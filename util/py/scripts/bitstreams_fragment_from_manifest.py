#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import jsonschema
import os
import sys

parser = argparse.ArgumentParser(
    description='Bitstream Manifest Fragment Extractor')
parser.add_argument('--manifest', required=True, help='Path to manifest file')
parser.add_argument('--schema', required=True, help='Path to validation schema')
parser.add_argument('--create-symlinks', default=False,
                    help='Populate files that the manifest refers to. If ' +
                         'symlinks are not created, another tool must ' +
                         'complete the entry with the expected directory ' +
                         'layout')
parser.add_argument('--design', required=True,
                    help='Name of the design to extract')
parser.add_argument('--out', required=True, help='Path to the output directory.')


def main(argv):
    args = parser.parse_args(args=argv[1:])
    with open(args.schema) as schema_file:
        schema = json.load(schema_file)
    with open(args.manifest, 'r') as manifest_file:
        manifest = json.load(manifest_file)
        jsonschema.validate(manifest, schema)

    # Extract only the indicated design.
    if args.design not in manifest['designs']:
        raise Exception('Design {} not present in manifest'.format(args.design))
    metadata = manifest['designs'][args.design]
    manifest['designs'] = {
        args.design: metadata
    }

    # Create symlinks to all the files if requested
    design_dir = os.path.join(args.out, args.design)
    os.makedirs(design_dir, exist_ok=True)

    # Replace the bitstream path.
    manifest_dir = os.path.dirname(os.path.realpath(args.manifest))
    bitstream = os.path.join(manifest_dir, metadata['bitstream']['file'])
    bitstream_renamed = os.path.join(args.design, os.path.basename(bitstream))
    metadata['bitstream']['file'] = bitstream_renamed
    if (args.create_symlinks):
        os.symlink(bitstream, os.path.join(args.out, bitstream_renamed))

    # Replace the MMI paths.
    for mmi in metadata['memory_map_info'].values():
        mmi_file = os.path.join(manifest_dir, mmi['file'])
        mmi_renamed = os.path.join(args.design, os.path.basename(mmi_file))
        mmi['file'] = mmi_renamed
        if (args.create_symlinks):
            os.symlink(mmi_file, os.path.join(args.out, mmi_renamed))

    # Dump the manifest to the specified location.
    manifest_path = os.path.join(args.out, 'manifest.json')
    with open(manifest_path, 'w') as manifest_file:
        json.dump(manifest, manifest_file, indent=True)


if __name__ == '__main__':
    sys.exit(main(sys.argv))
