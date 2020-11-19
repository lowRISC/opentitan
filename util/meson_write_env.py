#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""A helper used by Meson to write an environment file

The environment file follows Docker's `.env` file structure with key=value
pairs. See https://docs.docker.com/compose/env-file/#syntax-rules for details.
"""

import argparse
import sys


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--out-file',
                        '-o',
                        required=False,
                        type=argparse.FileType('w'),
                        default="env.txt",
                        help="Output file (default: %(default)s)")
    parser.add_argument('key_value_pairs',
                        nargs='+',
                        type=str,
                        metavar='NAME=VALUE')
    args = parser.parse_args()

    for arg in args.key_value_pairs:
        print(arg, file=args.out_file)

    print("Wrote environment configuration to {!r}.".format(args.out_file.name))

    return 0


if __name__ == "__main__":
    sys.exit(main())
