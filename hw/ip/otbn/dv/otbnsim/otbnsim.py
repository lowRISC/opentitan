#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Execute the simulation

import argparse
import struct
import sys

from sim.decode import decode_file
from sim.model import OTBNModel
from sim.sim import OTBNSim


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("imem_words", type=int)
    parser.add_argument("imem_file")
    parser.add_argument("dmem_words", type=int)
    parser.add_argument("dmem_file")
    parser.add_argument("cycles_file")
    parser.add_argument("trace_file")
    parser.add_argument("start_addr", type=int)

    args = parser.parse_args()
    sim = OTBNSim(OTBNModel(verbose=args.trace_file))

    sim.load_program(decode_file(args.imem_file))
    with open(args.dmem_file, "rb") as f:
        sim.load_data(f.read())

    cycles = sim.run(start_addr=args.start_addr)

    with open(args.dmem_file, "wb") as f:
        f.write(sim.dump_data())

    with open(args.cycles_file, "wb") as f:
        f.write(struct.pack("<L", cycles))

    return 0


if __name__ == '__main__':
    sys.exit(main())
