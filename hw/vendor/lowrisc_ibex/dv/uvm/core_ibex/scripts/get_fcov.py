#!/usr/bin/env python3
"""Get the riscv_dv functional coverage results."""

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import sys
import argparse
import pathlib3x as pathlib
import shutil

from metadata import RegressionMetadata, LockedMetadata
from scripts_lib import run_one
import riscvdv_interface

import logging
logger = logging.getLogger(__name__)


def _main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--dir-metadata', type=pathlib.Path, required=True)
    args = parser.parse_args()

    with LockedMetadata(args.dir_metadata, __file__) as md:
        md.dir_fcov.mkdir(exist_ok=True, parents=True)
        md.riscvdv_fcov_cmds = [riscvdv_interface.get_cov_cmd(md)]
        md.riscvdv_fcov_stdout = md.dir_fcov/'riscvdv_fcov_stdout.log'

    retcode = run_one(md.verbose, md.riscvdv_fcov_cmds[0], md.riscvdv_fcov_stdout)

    return retcode


if __name__ == '__main__':
    sys.exit(_main())
