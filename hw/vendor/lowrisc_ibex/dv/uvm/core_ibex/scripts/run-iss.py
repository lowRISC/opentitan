#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import sys
import tempfile

import construct_makefile
from scripts_lib import start_riscv_dv_run_cmd, run_one


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--verbose', action='store_true')
    parser.add_argument('--iss', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--isa', required=True)

    parser.add_argument('--test', required=True)
    parser.add_argument('--start-seed', type=int, required=True)
    parser.add_argument('--iterations', type=int, required=True)

    parser.add_argument('--pmp-num-regions', type=int, required=True)
    parser.add_argument('--pmp-granularity', type=int, required=True)

    args = parser.parse_args()

    iss_opts = []
    if args.iss == 'ovpsim':
        iss_opts += ['--override',
                     f'riscvOVPsim/cpu/PMP_registers={args.pmp_num_regions}',
                     '--override',
                     f'riscvOVPsim/cpu/PMP_grain={args.pmp_granularity}']

    output_makefile = os.path.join(args.output, 'iss.mk')

    with tempfile.NamedTemporaryFile() as tf:
        cmd = (start_riscv_dv_run_cmd(args.verbose) +
               ['--steps=iss_sim',
                '--output', args.output,
                '--isa', args.isa,
                '--iss', args.iss,
                '--test', args.test,
                '--start_seed', str(args.start_seed),
                '--iterations', str(args.iterations),
                '--debug', tf.name])
        if iss_opts:
            cmd += ['--iss_opts', ' '.join(iss_opts)]

        # Run riscv-dv to generate a bunch of commands
        gen_retcode = run_one(args.verbose, cmd)
        if gen_retcode:
            return gen_retcode

        # Now convert that command list to a Makefile
        construct_makefile.transform(False, tf.name, output_makefile)

    # Finally, run Make to run those commands
    cmd = ['make', '-f', output_makefile, 'all']
    if not args.verbose:
        cmd.append('-s')

    return run_one(args.verbose, cmd)


if __name__ == '__main__':
    sys.exit(main())
