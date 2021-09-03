#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys

from sim.elf import load_elf
from sim.sim import OTBNSim
from sim.stats import ExecutionStatAnalyzer


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('elf')
    parser.add_argument('-v', '--verbose', action='store_true')
    parser.add_argument(
        '--dump-dmem',
        metavar="FILE",
        type=argparse.FileType('wb'),
        help=("after execution, write the data memory contents to this file. "
              "Use '-' to write to STDOUT.")
    )
    parser.add_argument(
        '--dump-regs',
        metavar="FILE",
        type=argparse.FileType('w'),
        help=("after execution, write the GPR and WDR contents to this file. "
              "Use '-' to write to STDOUT.")
    )
    parser.add_argument(
        '--dump-stats',
        metavar="FILE",
        type=argparse.FileType('w'),
        help=("after execution, write execution statistics to this file. "
              "Use '-' to write to STDOUT.")
    )

    args = parser.parse_args()

    collect_stats = args.dump_stats is not None

    sim = OTBNSim()
    exp_end_addr = load_elf(sim, args.elf)

    sim.state.ext_regs.commit()

    sim.start()
    sim.run(verbose=args.verbose, collect_stats=collect_stats)

    if exp_end_addr is not None:
        if sim.state.pc != exp_end_addr:
            print('Run stopped at PC {:#x}, but _expected_end_addr was {:#x}.'
                  .format(sim.state.pc, exp_end_addr),
                  file=sys.stderr)
            return 1

    if args.dump_dmem is not None:
        args.dump_dmem.write(sim.dump_data())

    if args.dump_regs is not None:
        for idx, value in enumerate(sim.state.gprs.peek_unsigned_values()):
            args.dump_regs.write(' x{:<2} = 0x{:08x}\n'.format(idx, value))
        for idx, value in enumerate(sim.state.wdrs.peek_unsigned_values()):
            args.dump_regs.write(' w{:<2} = 0x{:064x}\n'.format(idx, value))

    if collect_stats:
        assert sim.stats is not None
        stat_analyzer = ExecutionStatAnalyzer(sim.stats, args.elf)
        args.dump_stats.write(stat_analyzer.dump())

    return 0


if __name__ == "__main__":
    sys.exit(main())
