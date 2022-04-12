#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys

from scripts_lib import start_riscv_dv_run_cmd, run_one


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--verbose', action='store_true')
    parser.add_argument('--output', required=True)
    parser.add_argument('--isa', required=True)

    parser.add_argument('--test', required=True)
    parser.add_argument('--start-seed', type=int, required=True)
    parser.add_argument('--iterations', type=int, required=True)

    args = parser.parse_args()

    cmd = (start_riscv_dv_run_cmd(args.verbose) +
           ['--output', args.output,
            '--steps=gcc_compile',
            '--test', args.test,
            '--start_seed', str(args.start_seed),
            '--iterations', str(args.iterations),
            '--isa', args.isa])
    if args.verbose:
        cmd.append('--verbose')

    return run_one(args.verbose, cmd)


if __name__ == '__main__':
    sys.exit(main())
