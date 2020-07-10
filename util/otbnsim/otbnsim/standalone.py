from riscvmodel.sim import Simulator
from .model import OTBNModel
from .variant import RV32IXotbn
from .asm import parse

import argparse
import sys

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("infile", nargs='?', type=argparse.FileType('r'), default=sys.stdin)
    args = parser.parse_args()

    sim = Simulator(OTBNModel(verbose=True))
    sim.load_program(parse(args.infile.read()))

    cycles = sim.run()

if __name__ == "__main__":
    main()
