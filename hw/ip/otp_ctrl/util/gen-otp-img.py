#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Generate RTL and documentation collateral from OTP memory
map definition file (hjson).
"""
import argparse
import logging as log
import random
from pathlib import Path

import hjson
from mako.template import Template

from OtpMemMap import OtpMemMap
from LcStEnc import LcStEnc
from common import wrapped_docstring

# TODO: some of these should be made into arguments.
# Image file definition.
IMAGE_DEFINITION_FILE = '../data/otp_ctrl_img_dev.hjson'

# Get the memory map definition.
MMAP_DEFINITION_FILE = '../data/otp_ctrl_mmap.hjson'
# Needed for the ECC polynomial and LC state defi
LC_STATE_DEFINITION_FILE = '../../lc_ctrl/data/lc_ctrl_state.hjson'
# This is needed for scrambling constants.
AUGMENTED_TOP_FILE = '../../../top_earlgrey/data/autogen/top_earlgrey.gen.hjson'


def main():
    log.basicConfig(level=log.INFO,
                    format="%(asctime)s - %(message)s",
                    datefmt="%Y-%m-%d %H:%M")

    parser = argparse.ArgumentParser(
        prog="gen-otp-img",
        description=wrapped_docstring(),
        formatter_class=argparse.RawDescriptionHelpFormatter)

    # TODO: think about re-seeding strategy for this.
    # # Generator options for compile time random netlist constants
    # parser.add_argument('--seed',
    #                     type=int,
    #                     metavar='<seed>',
    #                     help='Custom seed for RNG to compute default values.')

    args = parser.parse_args()

    img_config = {}
    lc_state_config = {}
    otp_mmap_config = {}
    top_config = {}

    with open(IMAGE_DEFINITION_FILE, 'r') as infile:
        img_config = hjson.load(infile)
    with open(LC_STATE_DEFINITION_FILE, 'r') as infile:
        lc_state_config = hjson.load(infile)
    with open(MMAP_DEFINITION_FILE, 'r') as infile:
        otp_mmap_config = hjson.load(infile)
    with open(AUGMENTED_TOP_FILE, 'r') as infile:
        top_config = hjson.load(infile)

    # TODO: make a class that pulls all this info together and
    # converts it into a hexdump for backloading OTP.
    log.info('Validate and generate life cycle state encoding')
    lc_state = LcStEnc(lc_state_config)
    log.info('')
    log.info('Validate and generate memory map')
    otp_mmap = OtpMemMap(otp_mmap_config)
    log.info('')

    # # If specified, override the seed for random image computations.
    # if args.seed:
    #     log.warning('Commandline override of seed with {}.'.format(
    #         args.seed))
    #     config['seed'] = args.seed
    # # Otherwise, we either take it from the .hjson if present, or
    # # randomly generate a new seed if not.
    # else:
    #     random.seed()
    #     new_seed = random.getrandbits(64)
    #     if config.setdefault('seed', new_seed) == new_seed:
    #         log.warning(
    #             'No seed specified, setting to {}.'.format(new_seed))

    # # Initialize RNG.
    # random.seed(int(config['seed']))






if __name__ == "__main__":
    main()
