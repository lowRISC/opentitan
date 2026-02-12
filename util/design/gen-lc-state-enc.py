#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
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

from lib.common import check_int, wrapped_docstring
from lib.LcStEnc import LcStEnc

# State encoding definition
LC_STATE_DEFINITION_FILE = "hw/ip/lc_ctrl/data/lc_ctrl_state.hjson"
# Code templates to render
TEMPLATES = ["hw/ip/lc_ctrl/rtl/lc_ctrl_state_pkg.sv.tpl"]


def _render_template(template: str, output_file: str, lc_st_enc: LcStEnc, top_secret_path: Path):
    with open(template, 'r') as tplfile:
        tpl = Template(tplfile.read())
        # Writing in binary mode with a large buffer size to improve performance
        # in cloud environments (i.e., CI). See #17574.
        if output_file:
            with open(output_file, 'wb', buffering=2097152) as outfile:
                outfile.write(tpl.render(lc_st_enc=lc_st_enc,
                                         top_secret_path=top_secret_path).encode('utf-8'))
        else:
            with open(Path(template).parent.joinpath(Path(template).stem),
                      'wb',
                      buffering=2097152) as outfile:
                outfile.write(tpl.render(lc_st_enc=lc_st_enc,
                                         top_secret_path=top_secret_path).encode('utf-8'))


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
    parser.add_argument('--top-secret-cfg',
                        type=Path,
                        metavar='<path>',
                        required=True,
                        help='''
                        Path to the top secret configuration in Hjson format.
                        ''')
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

    with open(args.top_secret_cfg, 'r') as infile:
        top_secret_cfg = hjson.load(infile)

    with open(args.lc_state_def_file, 'r') as infile:
        config = hjson.load(infile)

        # validate config and generate encoding
        try:
            lc_ctrl_seed = check_int(top_secret_cfg["seed"]["lc_ctrl_seed"]["value"])
            lc_st_enc = LcStEnc(config, lc_ctrl_seed)
        except RuntimeError as err:
            log.error(err)
            exit(1)

        # only generate the rust constants file if the template is provided
        if args.raw_unlock_rs_template:
            _render_template(args.raw_unlock_rs_template,
                             args.raw_unlock_rs_output, lc_st_enc, args.top_secret_cfg,)
        else:
            # otherwise, render all templates
            for template in TEMPLATES:
                _render_template(template, None, lc_st_enc, args.top_secret_cfg,)


if __name__ == "__main__":
    main()
