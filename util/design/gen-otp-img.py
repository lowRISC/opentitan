#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Generate RTL and documentation collateral from OTP memory
map definition file (hjson).
"""
import argparse
import datetime
import logging as log
from pathlib import Path

import hjson

from lib.common import vmem_permutation_string, wrapped_docstring
from lib.OtpMemImg import OtpMemImg

# Life cycle state and ECC poly definitions.
LC_STATE_DEFINITION_FILE = 'hw/ip/lc_ctrl/data/lc_ctrl_state.hjson'
# Default output path (can be overridden on the command line). Note that
# "BITWIDTH" will be replaced with the architecture's bitness.
MEMORY_MEM_FILE = 'otp-img.BITWIDTH.vmem'


def main():
    log.basicConfig(level=log.INFO, format="%(levelname)s: %(message)s")

    # Make sure the script can also be called from other dirs than
    # just the project root by adapting the default paths accordingly.
    proj_root = Path(__file__).parent.joinpath('../../')
    lc_state_def_file = Path(proj_root).joinpath(LC_STATE_DEFINITION_FILE)

    parser = argparse.ArgumentParser(
        prog="gen-otp-img",
        description=wrapped_docstring(),
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--quiet',
                        '-q',
                        action='store_true',
                        help='''Don't print out progress messages.''')
    parser.add_argument('--stamp',
                        action='store_true',
                        help='''
                        Add a comment 'Generated on [Date] with [Command]' to
                        generated output files.
                        ''')
    parser.add_argument('-o',
                        '--out',
                        type=str,
                        metavar='<path>',
                        default=MEMORY_MEM_FILE,
                        help='''
                        Custom output path for generated MEM file.
                        Defaults to {}
                        '''.format(MEMORY_MEM_FILE))
    parser.add_argument('--lc-state-def',
                        type=Path,
                        metavar='<path>',
                        default=lc_state_def_file,
                        help='''
                        Life cycle state definition file in Hjson format.
                        ''')
    parser.add_argument('--mmap-def',
                        type=Path,
                        metavar='<path>',
                        required=True,
                        help='''
                        Path to OTP memory map file in Hjson format.
                        ''')
    parser.add_argument('--top-secret-cfg',
                        type=Path,
                        metavar='<path>',
                        required=True,
                        help='''
                        Path to the top secret configuration in Hjson format.
                        ''')
    parser.add_argument('--img-cfg',
                        type=Path,
                        metavar='<path>',
                        required=True,
                        help='''
                        Image configuration file in Hjson format.
                        ''')
    parser.add_argument('--add-cfg',
                        type=Path,
                        metavar='<path>',
                        action='extend',
                        nargs='+',
                        default=[],
                        help='''
                        Additional image configuration file in Hjson format.

                        This switch can be specified multiple times.
                        Image configuration files are parsed in the same
                        order as they are specified on the command line,
                        and partition item values that are specified multiple
                        times are overridden in that order.

                        Note that seed values in additional configuration files
                        are ignored.
                        ''')
    parser.add_argument('--data-perm',
                        type=vmem_permutation_string,
                        metavar='<map>',
                        default='',
                        help='''
                        This is a post-processing option and allows permuting
                        the bit positions before writing the memfile.
                        The bit mapping needs to be supplied as a comma separated list
                        of bit slices, where the numbers refer to the bit positions in
                        the original data word before remapping, for example:

                        "[7:0],[15:8]".

                        The mapping must be bijective - otherwise this will generate
                        an error.
                        ''')
    parser.add_argument('--c-template',
                        type=Path,
                        metavar='<path>',
                        help='''
                        Template file used to generate C version of the OTP image.
                        This flag is only required when --c-out is set.
                        ''')
    parser.add_argument('--c-out',
                        type=Path,
                        metavar='<path>',
                        help='''
                        C output path. Requires the --c-template flag to be
                        set. The --out flag is ignored when this flag is set.
                        ''')

    args = parser.parse_args()

    if args.quiet:
        log.getLogger().setLevel(log.WARNING)

    log.info('Loading LC state definition file {}'.format(args.lc_state_def))
    with open(args.lc_state_def, 'r') as infile:
        lc_state_cfg = hjson.load(infile)
    log.info('Loading OTP memory map definition file {}'.format(args.mmap_def))
    with open(args.mmap_def, 'r') as infile:
        otp_mmap_cfg = hjson.load(infile)
    log.info('Loading main image configuration file {}'.format(args.img_cfg))
    with open(args.img_cfg, 'r') as infile:
        img_cfg = hjson.load(infile)
    log.info('Loading top secret configuration file {}'.format(args.top_secret_cfg))
    with open(args.top_secret_cfg, 'r') as infile:
        top_secret_cfg = hjson.load(infile)

    try:
        otp_mem_img = OtpMemImg(lc_state_cfg, otp_mmap_cfg, img_cfg,
                                args.data_perm, top_secret_cfg)

        for f in args.add_cfg:
            log.info(
                'Processing additional image configuration file {}'.format(f))
            log.info('')
            with open(f, 'r') as infile:
                cfg = hjson.load(infile)
                otp_mem_img.override_data(cfg)
            log.info('')

    except RuntimeError as err:
        log.error(err)
        exit(1)

    # Print all defined args into header comment for reference
    argstr = ''
    for arg, argval in sorted(vars(args).items()):
        if argval:
            if not isinstance(argval, list):
                argval = [argval]
            for a in argval:
                argname = '-'.join(arg.split('_'))
                # Get absolute paths for all files specified.
                a = a.resolve() if isinstance(a, Path) else a
                argstr += ' \\\n//   --' + argname + ' ' + str(a) + ''

    file_header = '//\n'
    if args.stamp:
        dt = datetime.datetime.now(datetime.timezone.utc)
        dtstr = dt.strftime("%a, %d %b %Y %H:%M:%S %Z")
        file_header = '// Generated on {} with\n// $ gen-otp-img.py {}\n//\n'.format(
            dtstr, argstr)

    if args.c_out:
        log.info(f'Generating C file: {args.c_out}')
        file_body = otp_mem_img.generate_c_file(file_header, args.c_template)
        with open(args.c_out, 'wb') as outfile:
            outfile.write(file_body.encode('utf-8'))
        exit(0)

    memfile_body, bitness = otp_mem_img.streamout_memfile()

    # If the out argument does not contain "BITWIDTH", it will not be changed.
    memfile_path = Path(args.out.replace('BITWIDTH', str(bitness)))

    # Use binary mode and a large buffer size to improve performance.
    with open(memfile_path, 'wb', buffering=2097152) as outfile:
        outfile.write(file_header.encode('utf-8'))
        outfile.write(memfile_body.encode('utf-8'))


if __name__ == "__main__":
    main()
