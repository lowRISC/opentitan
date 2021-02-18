#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys

from sim.elf import load_elf
from sim.sim import OTBNSim


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('elf')
    parser.add_argument('-v', '--verbose', action='store_true')
    parser.add_argument(
        '--dump-dmem',
        metavar="FILE",
        type=argparse.FileType('wb'),
        help="after execution, write the data memory contents to this file")
    parser.add_argument(
        '--dump-regs',
        metavar="FILE",
        type=argparse.FileType('w'),
        default=sys.stdout,
        help=
        "after execution, write the GPR and WDR contents to this file (default: STDOUT)"
    )

    args = parser.parse_args()

    sim = OTBNSim()
    load_elf(sim, args.elf)

    sim.state.pc = 0
    sim.state.start()
    sim.run(verbose=args.verbose)

    if args.dump_dmem is not None:
        args.dump_dmem.write(sim.dump_data())

    if args.dump_regs is not None:
        for idx, value in enumerate(sim.state.gprs.peek_unsigned_values()):
            args.dump_regs.write(' x{:<2} = 0x{:08x}\n'.format(idx, value))
        for idx, value in enumerate(sim.state.wdrs.peek_unsigned_values()):
            args.dump_regs.write(' w{:<2} = 0x{:064x}\n'.format(idx, value))

    return 0


if __name__ == "__main__":
    sys.exit(main())
