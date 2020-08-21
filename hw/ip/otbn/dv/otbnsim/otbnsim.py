#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Execute the simulation

import argparse
import struct
import sys

from riscvmodel.sim import Simulator  # type: ignore
from riscvmodel.model import Model  # type: ignore
from riscvmodel.variant import RV32I  # type: ignore

from sim.decode import decode_file


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("imem_words", type=int)
    parser.add_argument("imem_file")
    parser.add_argument("dmem_words", type=int)
    parser.add_argument("dmem_file")
    parser.add_argument("cycles_file")

    args = parser.parse_args()
    sim = Simulator(Model(RV32I))

    sim.load_program(decode_file(args.imem_file, RV32I))
    with open(args.dmem_file, "rb") as f:
        sim.load_data(f.read())

    cycles = sim.run()

    with open(args.dmem_file, "wb") as f:
        f.write(sim.dump_data())

    with open(args.cycles_file, "wb") as f:
        f.write(struct.pack("<L", cycles))

    return 0


if __name__ == '__main__':
    sys.exit(main())
