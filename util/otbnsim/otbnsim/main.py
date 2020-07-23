# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Execute the simulation

from riscvmodel.sim import Simulator
from riscvmodel.code import read_from_binary

import argparse
import struct

from .model import OTBNModel
from .insn import *


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("imem_words", type=int)
    parser.add_argument("imem_file")
    parser.add_argument("dmem_words", type=int)
    parser.add_argument("dmem_file")
    parser.add_argument("cycles_file")
    parser.add_argument("trace_file")

    args = parser.parse_args()
    sim = Simulator(OTBNModel(verbose=args.trace_file))

    sim.load_program(read_from_binary(args.imem_file, stoponerror=True))
    with open(args.dmem_file, "rb") as f:
        sim.load_data(f.read())

    cycles = sim.run()

    with open(args.dmem_file, "wb") as f:
        f.write(sim.dump_data())

    with open(args.cycles_file, "wb") as f:
        f.write(struct.pack("<L", cycles))
