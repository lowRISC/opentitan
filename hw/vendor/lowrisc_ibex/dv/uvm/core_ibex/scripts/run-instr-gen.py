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
    parser.add_argument('--simulator', required=True)
    parser.add_argument('--end-signature-addr', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--isa', required=True)

    parser.add_argument('--test', required=True)
    parser.add_argument('--start-seed', type=int, required=True)
    parser.add_argument('--iterations', type=int, required=True)

    parser.add_argument('--pmp-num-regions', type=int, required=True)
    parser.add_argument('--pmp-granularity', type=int, required=True)

    args = parser.parse_args()

    inst_overrides = [
        'riscv_asm_program_gen',
        'ibex_asm_program_gen',
        'uvm_test_top.asm_gen'
    ]
    sim_opts_dict = {
        'uvm_set_inst_override': ','.join(inst_overrides),
        'signature_addr': args.end_signature_addr,
        'pmp_num_regions': str(args.pmp_num_regions),
        'pmp_granularity': str(args.pmp_granularity),
        'tvec_alignment': '8'
    }
    sim_opts_str = ' '.join('+{}={}'.format(k, v)
                            for k, v in sim_opts_dict.items())

    output_makefile = os.path.join(args.output, 'run.mk')

    with tempfile.NamedTemporaryFile() as tf:
        cmd = (start_riscv_dv_run_cmd(args.verbose) +
               ['--so', '--steps=gen',
                '--output', args.output,
                '--simulator', args.simulator,
                '--isa', args.isa,
                '--test', args.test,
                '--start_seed', str(args.start_seed),
                '--iterations', str(args.iterations),
                '--sim_opts', sim_opts_str,
                '--debug', tf.name])

        # Run riscv-dv to generate a bunch of commands
        gen_retcode = run_one(args.verbose, cmd)
        if gen_retcode:
            return gen_retcode

        # Now convert that command list to a Makefile
        construct_makefile.transform(True, tf.name, output_makefile)

    # Finally, run Make to run those commands
    cmd = ['make', '-f', output_makefile, 'all']
    if not args.verbose:
        cmd.append('-s')

    return run_one(args.verbose, cmd)


if __name__ == '__main__':
    sys.exit(main())
