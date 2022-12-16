# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0


# Process dependent library wrapper generator that runs under bazel environment

import argparse
import os

from mako.template import Template

DESC = """primgen, generate process dependent library wrapper"""

USAGE = '''
  primgen.py [options]
  primgen.py (-h | --help)
'''
# lib_list: list of Path or FilType
def _generate_abstract_impl(lib_list) -> str:
    return ''

def main():
    parser = argparse.ArgumentParser(
        prog = "primgen",
        usage = USAGE,
        description = DESC)

    parser.add_argument('--output', '-o',
      metavar='file',
      type=argparse.FileType('w'),
      help='wrapper file path to generate')
    parser.add_argument('--lib', '-l',
      action='append', #-l 123 -l 1234
      required=True,
      metavar='file',
      type=argparse.FileType('r'),
      help='input lib modules')

    args = parser.parse_args()

    # TODO: Check lib list. `generic` is mandatory

    # Generate wrapper file
    with args.output:
        args.output.write(_generate_abstract_impl(lib_list=args.lib))


if __name__ == "__main__":
    main()
