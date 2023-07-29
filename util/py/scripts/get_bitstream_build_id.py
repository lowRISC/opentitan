#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import jsonschema
import sys

description = """Bitstream Build ID Query

Prints the build ID for the provided design in the manifest. If the design is
not found in the manifest, prints nothing.
"""

parser = argparse.ArgumentParser(description=description)

parser.add_argument('--manifest', required=True, help='Path to manifest file')
parser.add_argument('--schema', required=True, help='Path to validation schema')
parser.add_argument('--design', required=True,
                    help='Name of the design to query')


def main(argv):
    args = parser.parse_args(args=argv[1:])
    with open(args.schema) as schema_file:
        schema = json.load(schema_file)
    with open(args.manifest, 'r') as manifest_file:
        manifest = json.load(manifest_file)
        jsonschema.validate(manifest, schema)

    # Extract only the indicated design.
    if args.design not in manifest['designs']:
        return
    print(manifest['designs'][args.design]['build_id'])


if __name__ == '__main__':
    sys.exit(main(sys.argv))
