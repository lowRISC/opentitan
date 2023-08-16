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
from pathlib import Path

import hjson
from mako.template import Template

from lib.common import wrapped_docstring
from lib.LcStEnc import LcStEnc

# State encoding definition
LC_STATE_DEFINITION_FILE = "hw/ip/lc_ctrl/data/lc_ctrl_state.hjson"
# Code templates to render
TEMPLATES = ["hw/ip/lc_ctrl/rtl/lc_ctrl_state_pkg.sv.tpl"]


def _render_template(template: str, output_file: str, lc_st_enc: LcStEnc):
    with open(template, 'r') as tplfile:
        tpl = Template(tplfile.read())
        # Writing in binary mode with a large buffer size to improve performance
        # in cloud environments (i.e., CI). See #17574.
        if output_file:
            with open(output_file, 'wb', buffering=2097152) as outfile:
                outfile.write(tpl.render(lc_st_enc=lc_st_enc).encode('utf-8'))
        else:
            with open(Path(template).parent.joinpath(Path(template).stem),
                      'wb',
                      buffering=2097152) as outfile:
                outfile.write(tpl.render(lc_st_enc=lc_st_enc).encode('utf-8'))


def main():
    log.basicConfig(level=log.WARNING, format="%(levelname)s: %(message)s")

    parser = argparse.ArgumentParser(
        prog="gen-lc-state-enc",
        description=wrapped_docstring(),
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--lc-state-def-file',
                        type=str,
                        default=LC_STATE_DEFINITION_FILE,
                        help='State encoding definition file in HJSON format.')
    parser.add_argument('-s',
                        '--seed',
                        type=int,
                        metavar='<seed>',
                        help='Custom seed for RNG.')
    parser.add_argument(
        '--raw-unlock-rs-template',
        type=str,
        metavar='<template file path>',
        help='Rust source file template to write raw unlock token constant too.'
    )
    parser.add_argument(
        '--raw-unlock-rs-output',
        type=str,
        metavar='<Rust output file path>',
        help='Rust output file that contains the raw unlock token constants.')
    args = parser.parse_args()

    with open(args.lc_state_def_file, 'r') as infile:
        config = hjson.load(infile)

        # If specified, override the seed for random netlist constant computation.
        if args.seed:
            log.warning('Commandline override of seed with {}.'.format(
                args.seed))
            config['seed'] = args.seed
        # Otherwise we make sure a seed exists in the HJSON config file.
        elif 'seed' not in config:
            log.error('Seed not found in configuration HJSON.')
            exit(1)

        # validate config and generate encoding
        try:
            lc_st_enc = LcStEnc(config)
        except RuntimeError as err:
            log.error(err)
            exit(1)

        # only generate the rust constants file if the template is provided
        if args.raw_unlock_rs_template:
            _render_template(args.raw_unlock_rs_template,
                             args.raw_unlock_rs_output, lc_st_enc)
        else:
            # otherwise, render all templates
            for template in TEMPLATES:
                _render_template(template, None, lc_st_enc)


if __name__ == "__main__":
    main()
