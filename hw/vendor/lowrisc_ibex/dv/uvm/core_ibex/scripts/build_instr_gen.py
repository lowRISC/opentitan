#!/usr/bin/env python3
"""Build the random instruction generator, if it requires building."""

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import shutil
import sys
import pathlib3x as pathlib

from scripts_lib import run_one, format_to_cmd
import riscvdv_interface
from metadata import RegressionMetadata, LockedMetadata

import logging
logger = logging.getLogger(__name__)


def _main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--dir-metadata', type=pathlib.Path, required=True)
    args = parser.parse_args()

    with LockedMetadata(args.dir_metadata, __file__) as md:
        # Delete the output directory if it existed to ensure a clean build, then
        # create it. (The creation step is needed so that we can write our log file
        # in the directory from the outset).
        try:
            shutil.rmtree(md.dir_instruction_generator)
        except FileNotFoundError:
            pass

        md.dir_instruction_generator.mkdir(exist_ok=True, parents=True)
        md.riscvdv_build_stdout = md.dir_instruction_generator/'build_stdout.log'
        md.riscvdv_build_cmds = [format_to_cmd(
            riscvdv_interface.get_run_cmd(md.verbose) +
            ['--co', '--steps=gen',
             '--simulator', md.simulator,
             '--output', md.dir_instruction_generator,
             '--isa', md.isa_ibex,
             '--end_signature_addr', md.signature_addr])]

    retcode = run_one(md.verbose, md.riscvdv_build_cmds[0], redirect_stdstreams=md.riscvdv_build_stdout)

    return retcode


if __name__ == '__main__':
    sys.exit(_main())

