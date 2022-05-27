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
from pathlib import Path

from reggen import (gen_cheader, gen_dv, gen_fpv, gen_html, gen_json, gen_rtl,
                    gen_rust, gen_sec_cm_testplan, gen_selfdoc, gen_tock,
                    version)
from reggen.countermeasure import CounterMeasure
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
    parser.add_argument('-a',
                        '--alias',
                        type=Path,
                        default=None,
                        help='Alias register file in Hjson type')
    parser.add_argument('-S',
                        '--scrub',
                        default=False,
                        action='store_true',
                        help='Scrub alias register definition')
    parser.add_argument('--cdefines',
                        '-D',
                        action='store_true',
                        help='Output C defines header')
    parser.add_argument('--rust',
                        '-R',
                        action='store_true',
                        help='Output Rust constants')
    parser.add_argument('--tock',
                        action='store_true',
                        help='Output Tock constants')
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
    parser.add_argument('--sec-cm-testplan',
                        action='store_true',
                        help='Generate security countermeasures testplan.')
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
    parser.add_argument(
        '--dv-base-names',
        nargs="+",
        help='Names or prefix for the DV register classes from which '
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
    parser.add_argument('--quiet',
                        '-q',
                        action='store_true',
                        help='Log only errors, not warnings')
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
    parser.add_argument(
        '--version-stamp',
        type=str,
        default=None,
        help=
        'If version stamping, the location of workspace version stamp file.')

    args = parser.parse_args()

    if args.version:
        version.show_and_exit(__file__, ["Hjson", "Mako"])

    verbose = args.verbose
    if verbose:
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
    elif args.quiet:
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.ERROR)
    else:
        log.basicConfig(format="%(levelname)s: %(message)s")

    # Entries are triples of the form (arg, (fmt, dirspec)).
    #
    # arg is the name of the argument that selects the format. fmt is the
    # name of the format. dirspec is None if the output is a single file; if
    # the output needs a directory, it is a default path relative to the source
    # file (used when --outdir is not given).
    arg_to_format = [('j', ('json', None)), ('c', ('compact', None)),
                     ('d', ('html', None)), ('doc', ('doc', None)),
                     ('r', ('rtl', 'rtl')), ('s', ('dv', 'dv')),
                     ('f', ('fpv', 'fpv/vip')), ('cdefines', ('cdh', None)),
                     ('sec_cm_testplan', ('sec_cm_testplan', 'data')),
                     ('rust', ('rs', None)), ('tock', ('trs', None))]
    fmt = None
    dirspec = None
    for arg_name, spec in arg_to_format:
        if getattr(args, arg_name):
            if fmt is not None:
                log.error('Multiple output formats specified on '
                          'command line ({} and {}).'.format(fmt, spec[0]))
                sys.exit(1)
            fmt, dirspec = spec
    if fmt is None:
        fmt = 'hjson'

    infile = args.input

    # Split parameters into key=value pairs.
    raw_params = args.param.split(';') if args.param else []
    params = []
    for idx, raw_param in enumerate(raw_params):
        tokens = raw_param.split('=')
        if len(tokens) != 2:
            raise ValueError('Entry {} in list of parameter defaults to '
                             'apply is {!r}, which is not of the form '
                             'param=value.'.format(idx, raw_param))
        params.append((tokens[0], tokens[1]))

    # Define either outfile or outdir (but not both), depending on the output
    # format.
    outfile = None
    outdir = None
    if dirspec is None:
        if args.outdir is not None:
            log.error('The {} format expects an output file, '
                      'not an output directory.'.format(fmt))
            sys.exit(1)

        outfile = args.outfile
    else:
        if args.outfile is not sys.stdout:
            log.error('The {} format expects an output directory, '
                      'not an output file.'.format(fmt))
            sys.exit(1)

        if args.outdir is not None:
            outdir = args.outdir
        elif infile is not sys.stdin:
            outdir = str(Path(infile.name).parents[1].joinpath(dirspec))
        else:
            # We're using sys.stdin, so can't infer an output directory name
            log.error(
                'The {} format writes to an output directory, which '
                'cannot be inferred automatically if the input comes '
                'from stdin. Use --outdir to specify it manually.'.format(
                    fmt))
            sys.exit(1)

    version_stamp = {}
    if args.version_stamp is not None:
        with open(args.version_stamp, 'rt') as f:
            for line in f:
                k, v = line.strip().split(' ', 1)
                version_stamp[k] = v

    if fmt == 'doc':
        with outfile:
            gen_selfdoc.document(outfile)
        exit(0)

    srcfull = infile.read()

    try:
        obj = IpBlock.from_text(srcfull, params, infile.name)
    except ValueError as err:
        log.error(str(err))
        exit(1)

    # Parse and validate alias register definitions (this ensures that the
    # structure of the original register node and the alias register file is
    # identical).
    if args.alias is not None:
        try:
            obj.alias_from_path(args.scrub, args.alias)
        except ValueError as err:
            log.error(str(err))
            exit(1)
    else:
        if args.scrub:
            raise ValueError('The --scrub argument is only meaningful in '
                             'combination with the --alias argument')

    # If this block has countermeasures, we grep for RTL annotations in all
    # .sv implementation files and check whether they match up with what is
    # defined inside the Hjson.
    # Skip this check when generating DV code - its not needed.
    if fmt != 'dv':
        sv_files = Path(
            infile.name).parent.joinpath('..').joinpath('rtl').glob('*.sv')
        rtl_names = CounterMeasure.search_rtl_files(sv_files)
        obj.check_cm_annotations(rtl_names, infile.name)

    if args.novalidate:
        with outfile:
            gen_json.gen_json(obj, outfile, fmt)
            outfile.write('\n')
    else:
        if fmt == 'rtl':
            return gen_rtl.gen_rtl(obj, outdir)
        if fmt == 'sec_cm_testplan':
            return gen_sec_cm_testplan.gen_sec_cm_testplan(obj, outdir)
        if fmt == 'dv':
            return gen_dv.gen_dv(obj, args.dv_base_names, outdir)
        if fmt == 'fpv':
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
            if fmt == 'html':
                return gen_html.gen_html(obj, outfile)
            elif fmt == 'cdh':
                return gen_cheader.gen_cdefines(obj, outfile, src_lic,
                                                src_copy)
            elif fmt == 'rs':
                return gen_rust.gen_rust(obj, outfile, src_lic, src_copy)
            elif fmt == 'trs':
                return gen_tock.gen_tock(obj, outfile, infile.name, src_lic,
                                         src_copy, version_stamp)
            else:
                return gen_json.gen_json(obj, outfile, fmt)

            outfile.write('\n')


if __name__ == '__main__':
    sys.exit(main())
