#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Generate RTL and documentation collateral from OTP memory
map definition file (hjson).
"""
import argparse
import datetime
import logging as log
import random
from pathlib import Path

import hjson

from lib.common import vmem_permutation_string, wrapped_docstring
from lib.OtpMemImg import OtpMemImg

# Get the memory map definition.
MMAP_DEFINITION_FILE = 'hw/ip/otp_ctrl/data/otp_ctrl_mmap.hjson'
# Life cycle state and ECC poly definitions.
LC_STATE_DEFINITION_FILE = 'hw/ip/lc_ctrl/data/lc_ctrl_state.hjson'
# Default image file definition (can be overridden on the command line).
IMAGE_DEFINITION_FILE = 'hw/ip/otp_ctrl/data/otp_ctrl_img_dev.hjson'
# Default output path (can be overridden on the command line). Note that
# "BITWIDTH" will be replaced with the architecture's bitness.
MEMORY_MEM_FILE = 'otp-img.BITWIDTH.vmem'


def _override_seed(args, seed_name, entropy_buffer_name, config):
    '''Override the seed key in config with value specified in args'''
    arg_seed = getattr(args, seed_name)
    arg_entropy_buffer = None
    if entropy_buffer_name:
        arg_entropy_buffer = getattr(args, entropy_buffer_name)

    if arg_entropy_buffer:
        if arg_seed:
            log.error(
                "{} 'entropy_buffer' option cannot be used with {} 'seed' option"
                .format(entropy_buffer_name, seed_name))
            exit(1)
        else:
            config['entropy_buffer'] = arg_entropy_buffer
    else:
        # An override seed of 0 will not trigger the override, which is intended, as
        # the OTP-generation Bazel rule sets the default seed values to 0.
        if arg_seed:
            log.warning('Commandline override of {} with {}.'.format(
                seed_name, arg_seed))
            config['seed'] = arg_seed
        # Otherwise, we either take it from the .hjson if present, or
        # randomly generate a new seed if not.
        else:
            new_seed = random.getrandbits(64)
            if config.setdefault('seed', new_seed) == new_seed:
                log.warning('No {} specified, setting to {}.'.format(
                    seed_name, new_seed))


# TODO: this can be removed when we have moved to Python 3.8
# in all regressions, since the extend action is only available
# from that version onward.
# This workaround solution has been taken verbatim from
# https://stackoverflow.com/questions/41152799/argparse-flatten-the-result-of-action-append
class ExtendAction(argparse.Action):
    '''Extend action for the argument parser'''

    def __call__(self, parser, namespace, values, option_string=None):
        items = getattr(namespace, self.dest) or []
        items.extend(values)
        setattr(namespace, self.dest, items)


def main():
    log.basicConfig(level=log.INFO, format="%(levelname)s: %(message)s")

    # Make sure the script can also be called from other dirs than
    # just the project root by adapting the default paths accordingly.
    proj_root = Path(__file__).parent.joinpath('../../')
    lc_state_def_file = Path(proj_root).joinpath(LC_STATE_DEFINITION_FILE)
    mmap_def_file = Path(proj_root).joinpath(MMAP_DEFINITION_FILE)
    img_def_file = Path(proj_root).joinpath(IMAGE_DEFINITION_FILE)

    parser = argparse.ArgumentParser(
        prog="gen-otp-img",
        description=wrapped_docstring(),
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.register('action', 'extend', ExtendAction)
    parser.add_argument('--quiet',
                        '-q',
                        action='store_true',
                        help='''Don't print out progress messages.''')
    parser.add_argument('--seed',
                        type=int,
                        metavar='<seed>',
                        help="Custom seed used for randomization.")
    parser.add_argument('--img-seed',
                        type=int,
                        metavar='<seed>',
                        help='''
                        Custom seed for RNG to compute randomized items in OTP image.

                        Can be used to override the seed value specified in the image
                        config Hjson.
                        ''')
    parser.add_argument('--lc-seed',
                        type=int,
                        metavar='<seed>',
                        help='''
                        Custom seed for RNG to compute randomized life cycle netlist constants.

                        Note that this seed must coincide with the seed used for generating
                        the LC state encoding (gen-lc-state-enc.py).

                        This value typically does not need to be specified as it is taken from
                        the LC state encoding definition Hjson.
                        ''')
    parser.add_argument("--lc-entropy-buffer",
                        type=str,
                        metavar="<entropy buffer file path>",
                        help="""
                        A file with entropy used to fill the RNG when the
                        gen-lc-state-enc.py script was invoked.
                        """)
    parser.add_argument('--otp-seed',
                        type=int,
                        metavar='<seed>',
                        help='''
                        Custom seed for RNG to compute randomized OTP netlist constants.

                        Note that this seed must coincide with the seed used for generating
                        the OTP memory map (gen-otp-mmap.py).

                        This value typically does not need to be specified as it is taken from
                        the OTP memory map definition Hjson.
                        ''')
    parser.add_argument("--otp-entropy-buffer",
                        type=str,
                        metavar="<entropy buffer file path>",
                        help="""
                        A file with entropy used to fill the RNG when the
                        gen-otp-mmap.py script was invoked.
                        """)
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
                        default=mmap_def_file,
                        help='''
                        OTP memory map file in Hjson format.
                        ''')
    parser.add_argument('--img-cfg',
                        type=Path,
                        metavar='<path>',
                        default=img_def_file,
                        help='''
                        Image configuration file in Hjson format.
                        Defaults to {}
                        '''.format(img_def_file))
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
    parser.add_argument('--header-template',
                        type=Path,
                        metavar='<path>',
                        help='''
                        Template file used to generate C header version of the OTP image.
                        This flag is only required when --header-out is set.
                        ''')
    parser.add_argument('--header-out',
                        type=Path,
                        metavar='<path>',
                        help='''
                        C header output path. Requires the --header-template flag to be
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

    # Set the initial random seed so that the generated image is
    # deterministically randomized.
    random.seed(args.seed)

    # If specified, override the seeds.
    _override_seed(args, 'lc_seed', 'lc_entropy_buffer', lc_state_cfg)
    _override_seed(args, 'otp_seed', 'otp_entropy_buffer', otp_mmap_cfg)
    _override_seed(args, 'img_seed', None, img_cfg)

    try:
        otp_mem_img = OtpMemImg(lc_state_cfg, otp_mmap_cfg, img_cfg,
                                args.data_perm)

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

    dt = datetime.datetime.now(datetime.timezone.utc)
    dtstr = dt.strftime("%a, %d %b %Y %H:%M:%S %Z")
    file_header = '// Generated on {} with\n// $ gen-otp-img.py {}\n//\n'.format(
        dtstr, argstr)

    if args.header_out:
        log.info(f'Generating header file: {args.header_out}')
        file_body = otp_mem_img.generate_headerfile(args.header_out,
                                                    file_header,
                                                    args.header_template)
        with open(args.header_out, 'wb') as outfile:
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
