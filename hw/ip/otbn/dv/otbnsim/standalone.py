#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys

from riscvmodel.sim import Simulator  # type: ignore
from riscvmodel.model import Model  # type: ignore
from riscvmodel.variant import RV32I  # type: ignore

from sim.elf import load_elf


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('elf')
    parser.add_argument('-v', '--verbose', action='store_true')
    parser.add_argument('--dmem-dump')

    args = parser.parse_args()

    sim = Simulator(Model(RV32I, verbose=args.verbose))
    load_elf(sim, args.elf)

    sim.run()

    if args.dmem_dump is not None:
        try:
            with open(args.dmem_dump, 'wb') as dmem_file:
                dmem_file.write(sim.dump_data())
        except OSError as err:
            sys.stderr.write('Failed to write DMEM to {!r}: {}.'
                             .format(args.dmem_dump, err))
            return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
