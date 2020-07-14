# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from riscvmodel.sim import Simulator
from .model import OTBNModel
from .variant import RV32IXotbn
from .asm import parse

import argparse
import sys


def run(program, data=[], *, verbose=True):
    sim = Simulator(OTBNModel(verbose=verbose))
    sim.load_program(program)
    sim.load_data(data)
    sim.run()
    return sim.dump_data()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("program",
                        nargs='?',
                        type=argparse.FileType('r'),
                        default=sys.stdin)
    parser.add_argument("data", nargs='?', type=argparse.FileType('rb'))
    args = parser.parse_args()

    run(parse(args.program.read()), args.data.read() if args.data else [])


if __name__ == "__main__":
    main()
