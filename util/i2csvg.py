#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Command-line tool to convert i2c to svg
"""

import argparse
import logging as log
import sys
from pathlib import PurePath

import pkg_resources  # part of setuptools

from i2csvg import convert
from reggen import version

ep = """defaults or the filename - can be used for stdin/stdout
By default all input files are concatenated into a single output file
this can be changed with the --multiout flag.
"""


def main():
    done_stdin = False
    parser = argparse.ArgumentParser(
        prog="i2csvg.py",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=__doc__,
        epilog=ep)
    parser.add_argument('--version',
                        action='store_true',
                        help='Show version and exit')
    parser.add_argument('-v',
                        '--verbose',
                        action='store_true',
                        help='Verbose output during processing')
    parser.add_argument('-d',
                        '--debug',
                        action='store_true',
                        help='Include internal representation in output file')
    parser.add_argument('-t',
                        '--text',
                        action='store_true',
                        help='Include text output in output file')
    parser.add_argument('-n',
                        '--nosvg',
                        action='store_true',
                        help="Don't include svg in output")

    parser.add_argument('-f',
                        '--fifodata',
                        action='store_true',
                        help='Data is hexdump of writes to FDATA fifo')
    parser.add_argument(
        '-p',
        '--prefix',
        action='store',
        help='Only process lines with this prefix (the prefix is removed)')
    parser.add_argument(
        '-m',
        '--multiout',
        action='store_true',
        help='Generate separate output file with .svg extension from inputs')
    parser.add_argument('-o',
                        '--output',
                        type=argparse.FileType('w'),
                        default=sys.stdout,
                        metavar='file',
                        help='Output file (default stdout)')
    parser.add_argument('srcfile',
                        nargs='*',
                        metavar='input',
                        default='-',
                        help='source i2c file (default stdin)')
    args = parser.parse_args()

    if args.version:
        version.show_and_exit(__file__, ["Hjson"])

    if (args.verbose):
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(levelname)s: %(message)s")

    outfile = args.output
    # output will be:
    # .svg if a single input file and no additional details (debug/text)
    #      or --multiout and no additional details
    # .html if combining multiple files (not --multiout) or additional details
    # .txt if --nosvg
    combiningfiles = (len(args.srcfile) > 1) and not args.multiout
    extrainfo = args.debug or args.text or combiningfiles

    if args.nosvg:
        makehtml = False
        outext = '.txt'
    elif extrainfo:
        makehtml = True
        outext = '.html'
    else:
        makehtml = False
        outext = '.svg'

    with outfile:
        for filename in args.srcfile:
            if (filename == '-'):
                if (done_stdin):
                    log.warn("Ignore stdin after first use\n")
                    continue
                done_stdin = True
                infile = sys.stdin
            else:
                infile = open(filename, 'r', encoding='UTF-8')
            with infile:
                log.info("\nFile now " + filename)
                if args.multiout:
                    outfname = str(PurePath(filename).with_suffix('.svg'))
                    outf = open(outfname, 'w', encoding='UTF-8')
                else:
                    outf = outfile
                if makehtml:
                    outf.write("<H2>" + filename + "</H2>")
                tr = convert.parse_file(infile, args.fifodata, args.prefix)
                if args.debug:
                    convert.output_debug(outf, tr,
                                         '<br>\n' if makehtml else '\n')
                    outf.write('<br>\n' if makehtml else '\n')
                if args.text:
                    if makehtml:
                        outf.write("<pre>\n")
                    convert.output_text(outf, tr,
                                        '<br>\n' if makehtml else '\n')
                    if makehtml:
                        outf.write("</pre>\n")
                if not args.nosvg:
                    convert.output_svg(outf, tr, makehtml)

                if args.multiout:
                    outf.close()


if __name__ == '__main__':
    main()
