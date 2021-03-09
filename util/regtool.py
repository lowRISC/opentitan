#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Command-line tool to validate and convert register hjson

"""
import argparse
import logging as log
import re
import sys
from pathlib import PurePath

from reggen import (gen_cheader, gen_dv, gen_fpv, gen_html,
                    gen_json, gen_rtl, gen_selfdoc, version)
from reggen.ip_block import IpBlock

DESC = """regtool, generate register info from Hjson source"""

USAGE = '''
  regtool [options]
  regtool [options] <input>
  regtool (-h | --help)
  regtool (-V | --version)
'''


def main():
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
    parser.add_argument('--outdir',
                        '-t',
                        help='Target directory for generated RTL; '
                        'tool uses ../rtl if blank.')
    parser.add_argument('--dv-base-prefix',
                        default='dv_base',
                        help='Prefix for the DV register classes from which '
                        'the register models are derived.')
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
    if (verbose):
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(levelname)s: %(message)s")

    # Entries are triples of the form (arg, (format, dirspec)).
    #
    # arg is the name of the argument that selects the format. format is the
    # name of the format. dirspec is None if the output is a single file; if
    # the output needs a directory, it is a default path relative to the source
    # file (used when --outdir is not given).
    arg_to_format = [('j', ('json', None)), ('c', ('compact', None)),
                     ('d', ('html', None)), ('doc', ('doc', None)),
                     ('r', ('rtl', 'rtl')), ('s', ('dv', 'dv')),
                     ('f', ('fpv', 'fpv/vip')), ('cdefines', ('cdh', None))]
    format = None
    dirspec = None
    for arg_name, spec in arg_to_format:
        if getattr(args, arg_name):
            if format is not None:
                log.error('Multiple output formats specified on '
                          'command line ({} and {}).'.format(format, spec[0]))
                sys.exit(1)
            format, dirspec = spec
    if format is None:
        format = 'hjson'

    infile = args.input

    # Split parameters into key=value pairs.
    raw_params = args.param.split(';') if args.param else []
    params = []
    for idx, raw_param in enumerate(raw_params):
        tokens = raw_param.split('=')
        if len(tokens) != 2:
            raise ValueError('Entry {} in list of parameter defaults to '
                             'apply is {!r}, which is not of the form '
                             'param=value.'
                             .format(idx, raw_param))
        params.append((tokens[0], tokens[1]))

    # Define either outfile or outdir (but not both), depending on the output
    # format.
    outfile = None
    outdir = None
    if dirspec is None:
        if args.outdir is not None:
            log.error('The {} format expects an output file, '
                      'not an output directory.'.format(format))
            sys.exit(1)

        outfile = args.outfile
    else:
        if args.outfile is not sys.stdout:
            log.error('The {} format expects an output directory, '
                      'not an output file.'.format(format))
            sys.exit(1)

        if args.outdir is not None:
            outdir = args.outdir
        elif infile is not sys.stdin:
            outdir = str(PurePath(infile.name).parents[1].joinpath(dirspec))
        else:
            # We're using sys.stdin, so can't infer an output directory name
            log.error(
                'The {} format writes to an output directory, which '
                'cannot be inferred automatically if the input comes '
                'from stdin. Use --outdir to specify it manually.'.format(
                    format))
            sys.exit(1)

    if format == 'doc':
        with outfile:
            gen_selfdoc.document(outfile)
        exit(0)

    srcfull = infile.read()

    try:
        obj = IpBlock.from_text(srcfull, params, infile.name)
    except ValueError as err:
        log.error(str(err))
        exit(1)

    if args.novalidate:
        with outfile:
            gen_json.gen_json(obj, outfile, format)
            outfile.write('\n')
    else:
        if format == 'rtl':
            return gen_rtl.gen_rtl(obj, outdir)
        if format == 'dv':
            return gen_dv.gen_dv(obj, args.dv_base_prefix, outdir)
        if format == 'fpv':
            return gen_fpv.gen_fpv(obj, outdir)
        src_lic = None
        src_copy = ''
        found_spdx = None
        found_lunder = None
        copy = re.compile(r'.*(copyright.*)|(.*\(c\).*)', re.IGNORECASE)
        spdx = re.compile(r'.*(SPDX-License-Identifier:.+)')
        lunder = re.compile(r'.*(Licensed under.+)', re.IGNORECASE)
        for line in srcfull.splitlines():
            mat = copy.match(line)
            if mat is not None:
                src_copy += mat.group(1)
            mat = spdx.match(line)
            if mat is not None:
                found_spdx = mat.group(1)
            mat = lunder.match(line)
            if mat is not None:
                found_lunder = mat.group(1)
        if found_lunder:
            src_lic = found_lunder
        if found_spdx:
            src_lic += '\n' + found_spdx

        with outfile:
            if format == 'html':
                return gen_html.gen_html(obj, outfile)
            elif format == 'cdh':
                return gen_cheader.gen_cdefines(obj, outfile, src_lic, src_copy)
            else:
                return gen_json.gen_json(obj, outfile, format)

            outfile.write('\n')


if __name__ == '__main__':
    sys.exit(main())
