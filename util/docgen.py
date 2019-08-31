#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Command-line tool to merge markdown and register spec to html

"""
import argparse
import logging as log
import os.path
import shutil
import sys

from pkg_resources import resource_filename

from docgen import generate, html_data, lowrisc_renderer
from reggen import version

USAGE = """
  docgen [options]
  docgen [options] <file>
  docgen (-h | --help)
  docgen --version
"""


def main():
    parser = argparse.ArgumentParser(
        prog="docgen",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        usage=USAGE,
        description=__doc__,
        epilog='defaults or the filename - can be used for stdin/stdout')
    parser.add_argument(
        '--version', action='store_true', help='Show version and exit')
    parser.add_argument(
        '-v',
        '--verbose',
        action='store_true',
        help='Verbose output during processing')
    parser.add_argument(
        '-c',
        '--inline-css',
        action='store_true',
        help='Put CSS inline in output file')
    parser.add_argument(
        '-d',
        '--asdiv',
        action='store_true',
        help='Output as a <div> without html header/trailer')
    parser.add_argument(
        '-j',
        '--wavesvg-usejs',
        action='store_true',
        help='Waveforms should use javascript wavedrom '
        'rather than generating inline svg')
    parser.add_argument(
        '-o',
        '--output',
        type=argparse.FileType('w'),
        default=sys.stdout,
        metavar='file',
        help='Output file (default stdout)')
    parser.add_argument(
        'srcfile',
        nargs='?',
        metavar='file',
        default='-',
        help='source markdown file (default stdin)')
    args = parser.parse_args()

    if args.version:
        version.show_and_exit(__file__, ["Hjson", "Mistletoe"])

    if (args.verbose):
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(levelname)s: %(message)s")

    outfile = args.output

    with outfile:
        outfile.write(
            generate.generate_doc(args.srcfile, args.verbose, args.inline_css,
                                  not args.wavesvg_usejs, args.asdiv))


if __name__ == '__main__':
    main()
