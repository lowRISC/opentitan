from riscvmodel.sim import Simulator
from riscvmodel.model import Model
from riscvmodel.variant import RV32I
from riscvmodel.code import read_from_binary, MachineDecodeError

import argparse

def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("imem_words", type=int)
  parser.add_argument("imem_file")
  parser.add_argument("dmem_words", type=int)
  parser.add_argument("dmem_file")
  args = parser.parse_args()
  sim = Simulator(Model(RV32I))

  sim.load_program(read_from_binary(args.imem_file, stoponerror=True))
  with open(args.dmem_file, "rb") as f:
    sim.load_data(f.read())

  sim.run()

  with open(args.dmem_file, "wb") as f:
    f.write(sim.dump_data())
