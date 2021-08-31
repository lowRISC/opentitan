#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Given an ECC encoding matrix, this script generates random life cycle
state encodings that can be incrementally written to a memory protected with
the ECC code specified.
"""
import argparse
import logging as log
import random
from pathlib import Path

import hjson
from lib.common import wrapped_docstring
from lib.LcStEnc import LcStEnc
from mako.template import Template

# State encoding definition
LC_STATE_DEFINITION_FILE = "hw/ip/lc_ctrl/data/lc_ctrl_state.hjson"
# Code templates to render
TEMPLATES = ["hw/ip/lc_ctrl/rtl/lc_ctrl_state_pkg.sv.tpl"]


def main():
    log.basicConfig(level=log.WARNING,
                    format="%(levelname)s: %(message)s")

    parser = argparse.ArgumentParser(
        prog="gen-lc-state-enc",
        description=wrapped_docstring(),
        formatter_class=argparse.RawDescriptionHelpFormatter)

    parser.add_argument('-s',
                        '--seed',
                        type=int,
                        metavar='<seed>',
                        help='Custom seed for RNG.')
    args = parser.parse_args()

    with open(LC_STATE_DEFINITION_FILE, 'r') as infile:
        config = hjson.load(infile)

        # If specified, override the seed for random netlist constant computation.
        if args.seed:
            log.warning('Commandline override of seed with {}.'.format(
                args.seed))
            config['seed'] = args.seed
        # Otherwise, we either take it from the .hjson if present, or
        # randomly generate a new seed if not.
        else:
            random.seed()
            new_seed = random.getrandbits(64)
            if config.setdefault('seed', new_seed) == new_seed:
                log.warning(
                    'No seed specified, setting to {}.'.format(new_seed))

        # validate config and generate encoding
        try:
            lc_st_enc = LcStEnc(config)
        except RuntimeError as err:
            log.error(err)
            exit(1)

        # render all templates
        for template in TEMPLATES:
            with open(template, 'r') as tplfile:
                tpl = Template(tplfile.read())
                with open(
                        Path(template).parent.joinpath(Path(template).stem),
                        'w') as outfile:
                    outfile.write(tpl.render(lc_st_enc=lc_st_enc))


if __name__ == "__main__":
    main()
