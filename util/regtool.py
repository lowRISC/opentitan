#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Command-line tool to validate and convert register hjson

"""
import argparse
import logging as log
import os
import re
import sys
from pathlib import PurePath

import hjson
import pkg_resources

from reggen import (gen_cheader, gen_ctheader, gen_dv, gen_html, gen_json,
                    gen_rtl, gen_fpv, gen_selfdoc, validate, version)

DESC = """regtool, generate register info from Hjson source"""

USAGE = '''
  regtool [options]
  regtool [options] <input>
  regtool (-h | --help)
  regtool (-V | --version)
'''


def main():
    format = 'hjson'
    verbose = 0

    parser = argparse.ArgumentParser(
        prog="regtool",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        usage=USAGE,
        description=DESC)
    parser.add_argument('input',
                        nargs='?',
                        metavar='file',
                        type=argparse.FileType('r'),
                        default=sys.stdin,
                        help='input file in Hjson type')
    parser.add_argument('-d',
                        action='store_true',
                        help='Output register documentation (html)')
    parser.add_argument('--cdefines',
                        '-D',
                        action='store_true',
                        help='Output C defines header')
    parser.add_argument('--ctdefines',
                        '-T',
                        action='store_true',
                        help='Output C defines header (Titan style)')
    parser.add_argument('--doc',
                        action='store_true',
                        help='Output source file documentation (gfm)')
    parser.add_argument('-j',
                        action='store_true',
                        help='Output as formatted JSON')
    parser.add_argument('-c', action='store_true', help='Output as JSON')
    parser.add_argument('-r',
                        action='store_true',
                        help='Output as SystemVerilog RTL')
    parser.add_argument('-s',
                        action='store_true',
                        help='Output as UVM Register class')
    parser.add_argument('-f',
                        action='store_true',
                        help='Output as FPV CSR rw assertion module')
    parser.add_argument('--outdir', '-t',
                        help='Target directory for generated RTL, '\
                             'tool uses ../rtl if blank.')
    parser.add_argument('--outfile',
                        '-o',
                        type=argparse.FileType('w'),
                        default=sys.stdout,
                        help='Target filename for json, html, gfm.')
    parser.add_argument('--verbose',
                        '-v',
                        action='store_true',
                        help='Verbose and run validate twice')
    parser.add_argument('--param',
                        '-p',
                        type=str,
                        default="",
                        help='''Change the Parameter values.
                                Only integer value is supported.
                                You can add multiple param arguments.

                                  Format: ParamA=ValA;ParamB=ValB
                                  ''')
    parser.add_argument('--version',
                        '-V',
                        action='store_true',
                        help='Show version')
    parser.add_argument('--novalidate',
                        action='store_true',
                        help='Skip validate, just output json')

    args = parser.parse_args()

    if args.version:
        version.show_and_exit(__file__, ["Hjson", "Mako"])

    verbose = args.verbose

    if args.j: format = 'json'
    elif args.c: format = 'compact'
    elif args.d: format = 'html'
    elif args.doc: format = 'doc'
    elif args.r: format = 'rtl'
    elif args.s: format = 'dv'
    elif args.f: format = 'fpv'
    elif args.cdefines: format = 'cdh'
    elif args.ctdefines: format = 'cth'

    if (verbose):
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(levelname)s: %(message)s")

    outfile = args.outfile

    infile = args.input

    params = args.param.split(';')

    if format == 'rtl':
        if args.outdir:
            outdir = args.outdir
        elif infile != sys.stdin:
            outdir = str(PurePath(infile.name).parents[1].joinpath("rtl"))
        else:
            # Using sys.stdin. not possible to generate RTL
            log.error("-r option cannot be used with pipe or stdin")
    elif format == 'dv':
        if args.outdir:
            outdir = args.outdir
        elif infile != sys.stdin:
            outdir = str(PurePath(infile.name).parents[1].joinpath("dv"))
        else:
            # Using sys.stdin. not possible to generate RTL
            log.error("-s option cannot be used with pipe or stdin")
    elif format == 'fpv':
        if args.outdir:
            outdir = args.outdir
        elif infile != sys.stdin:
            outdir = str(PurePath(infile.name).parents[1].joinpath("fpv/vip"))
        else:
            # Using sys.stdin. not possible to generate RTL
            log.error("-s option cannot be used with pipe or stdin")
    else:
        # Ignore
        outdir = "."

    if format == 'doc':
        with outfile:
            gen_selfdoc.document(outfile)
        exit(0)

    with infile:
        try:
            srcfull = infile.read()
            obj = hjson.loads(srcfull,
                              use_decimal=True,
                              object_pairs_hook=validate.checking_dict)
        except ValueError:
            raise SystemExit(sys.exc_info()[1])

    if args.novalidate:
        with outfile:
            gen_json.gen_json(obj, outfile, format)
            outfile.write('\n')
    elif (validate.validate(obj, params=params) == 0):
        if (verbose):
            log.info("Second validate pass (should show added optional keys)")
            validate.validate(obj, params=params)

        if format == 'rtl':
            gen_rtl.gen_rtl(obj, outdir)
            return 0
        if format == 'dv':
            gen_dv.gen_dv(obj, outdir)
            return 0
        if format == 'fpv':
            gen_fpv.gen_fpv(obj, outdir)
            return 0
        src_lic = None
        src_copy = ''
        found_spdx = None
        found_lunder = None
        copy = re.compile(r'.*(copyright.*)|(.*\(c\).*)', re.IGNORECASE)
        spdx = re.compile(r'.*(SPDX-License-Identifier:.+)')
        lunder = re.compile(r'.*(Licensed under.+)', re.IGNORECASE)
        for line in srcfull.splitlines():
            mat = copy.match(line)
            if mat != None:
                src_copy += mat.group(1)
            mat = spdx.match(line)
            if mat != None:
                found_spdx = mat.group(1)
            mat = lunder.match(line)
            if mat != None:
                found_lunder = mat.group(1)
        if found_lunder:
            src_lic = found_lunder
        if found_spdx:
            src_lic += '\n' + found_spdx

        with outfile:
            if format == 'html':
                gen_html.gen_html(obj, outfile)
            elif format == 'cdh':
                gen_cheader.gen_cdefines(obj, outfile, src_lic, src_copy)
            elif format == 'cth':
                gen_ctheader.gen_cdefines(obj, outfile, src_lic, src_copy)
            else:
                gen_json.gen_json(obj, outfile, format)

            outfile.write('\n')


if __name__ == '__main__':
    main()
