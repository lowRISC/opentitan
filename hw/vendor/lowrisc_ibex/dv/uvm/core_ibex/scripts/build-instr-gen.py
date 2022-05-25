#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys

from scripts_lib import run_one, start_riscv_dv_run_cmd


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--verbose', action='store_true')
    parser.add_argument('--simulator', required=True)
    parser.add_argument('--end-signature-addr', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--isa', required=True)

    args = parser.parse_args()

    cmd = (start_riscv_dv_run_cmd(args.verbose) +
           ['--co', '--steps=gen',
            '--simulator', args.simulator,
            '--output', args.output,
            '--isa', args.isa,
            '--end_signature_addr', args.end_signature_addr])

    return run_one(args.verbose, cmd)


if __name__ == '__main__':
    sys.exit(main())
