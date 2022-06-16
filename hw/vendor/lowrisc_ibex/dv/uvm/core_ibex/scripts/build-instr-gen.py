#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import shutil
import sys

from scripts_lib import (run_one, start_riscv_dv_run_cmd,
                         get_config, get_isas_for_config)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--verbose', action='store_true')
    parser.add_argument('--simulator', required=True)
    parser.add_argument('--end-signature-addr', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--ibex-config', required=True)

    args = parser.parse_args()

    # Delete the output directory if it existed to ensure a clean build, then
    # create it. (The creation step is needed so that we can write our log file
    # in the directory from the outset).
    try:
        shutil.rmtree(args.output)
    except FileNotFoundError:
        pass

    os.makedirs(args.output, exist_ok=True)

    cfg = get_config(args.ibex_config)
    isa, iss_isa = get_isas_for_config(cfg)

    cmd = (start_riscv_dv_run_cmd(args.verbose) +
           ['--co', '--steps=gen',
            '--simulator', args.simulator,
            '--output', args.output,
            '--isa', isa,
            '--end_signature_addr', args.end_signature_addr])

    log_path = os.path.join(args.output, 'build.log')
    return run_one(args.verbose, cmd, redirect_stdstreams=log_path)


if __name__ == '__main__':
    sys.exit(main())
