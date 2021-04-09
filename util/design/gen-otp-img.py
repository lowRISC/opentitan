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
from lib.common import wrapped_docstring
from lib.OtpMemImg import OtpMemImg

# Get the memory map definition.
MMAP_DEFINITION_FILE = 'hw/ip/otp_ctrl/data/otp_ctrl_mmap.hjson'
# Life cycle state and ECC poly definitions.
LC_STATE_DEFINITION_FILE = 'hw/ip/lc_ctrl/data/lc_ctrl_state.hjson'
# Default image file definition (can be overridden on the command line).
IMAGE_DEFINITION_FILE = 'hw/ip/otp_ctrl/data/otp_ctrl_img_dev.hjson'
# Default output path (can be overridden on the command line).
MEMORY_HEX_FILE = 'otp-img.vmem'


def _override_seed(args, name, config):
    '''Override the seed key in config with value specified in args'''
    arg_seed = getattr(args, name)
    if arg_seed:
        log.warning('Commandline override of {} with {}.'.format(
            name, arg_seed))
        config['seed'] = arg_seed
    # Otherwise, we either take it from the .hjson if present, or
    # randomly generate a new seed if not.
    else:
        random.seed()
        new_seed = random.getrandbits(64)
        if config.setdefault('seed', new_seed) == new_seed:
            log.warning('No {} specified, setting to {}.'.format(
                name, new_seed))


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
    hex_file = Path(MEMORY_HEX_FILE)

    parser = argparse.ArgumentParser(
        prog="gen-otp-img",
        description=wrapped_docstring(),
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.register('action', 'extend', ExtendAction)
    parser.add_argument('--quiet', '-q', action='store_true',
                        help='''Don't print out progress messages.''')
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
    parser.add_argument('-o',
                        '--out',
                        type=Path,
                        metavar='<path>',
                        default=hex_file,
                        help='''
                        Custom output path for generated hex file.
                        Defaults to {}
                        '''.format(hex_file))
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

    args = parser.parse_args()

    if args.quiet:
        log.getLogger().setLevel(log.WARNING)

    log.info('Loading LC state definition file {}'.format(lc_state_def_file))
    with open(lc_state_def_file, 'r') as infile:
        lc_state_cfg = hjson.load(infile)
    log.info('Loading OTP memory map definition file {}'.format(mmap_def_file))
    with open(mmap_def_file, 'r') as infile:
        otp_mmap_cfg = hjson.load(infile)
    log.info('Loading main image configuration file {}'.format(args.img_cfg))
    with open(args.img_cfg, 'r') as infile:
        img_cfg = hjson.load(infile)

    # If specified, override the seeds.
    _override_seed(args, 'lc_seed', lc_state_cfg)
    _override_seed(args, 'otp_seed', otp_mmap_cfg)
    _override_seed(args, 'img_seed', img_cfg)

    try:
        otp_mem_img = OtpMemImg(lc_state_cfg, otp_mmap_cfg, img_cfg)

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

    # Print all defined args into header comment for referqence
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
    memfile_header = '// Generated on {} with\n// $ gen-otp-img.py {}\n//\n'.format(
        dtstr, argstr)

    hexfile_content = memfile_header + otp_mem_img.streamout_hexfile()

    with open(args.out, 'w') as outfile:
        outfile.write(hexfile_content)


if __name__ == "__main__":
    main()
