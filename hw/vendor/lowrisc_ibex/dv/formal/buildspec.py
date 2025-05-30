# Copyright lowRISC contributors.
# Copyright 2024 University of Oxford, see also CREDITS.md.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# Original author: Louis-Emile Ploix
# SPDX-License-Identifier: Apache-2.0

# This script is called from the Makefile.
# Essentially it is a way to enable and disable instructions from the Sail specification to make proofs easier.

import json
import re
import sys

with open("instrs.json", "r") as f:
    INSTRS = set(json.load(f))

class SpecConfig:
    def __init__(self):
        self.instrs = set()

    def add(self, *instrs):
        for instr in instrs:
            assert instr in INSTRS
            self.instrs.add(instr)

    def add_all(self):
        self.instrs = INSTRS

    def add_noncompressed(self):
        self.instrs = {x for x in INSTRS if not x.startswith("C_")}

    def remove(self, instr):
        assert instr in INSTRS
        self.instrs.discard(instr)

    def make_sail_unreachables(self):
        return " ".join(f"-sv_unreachable execute_{instr}" for instr in INSTRS.difference(self.instrs))

    def make_sv_header(self):
        return "\n".join([
            "`ifndef SPEC_INSTRS",
            "`define SPEC_INSTRS",
            "",
            *[f"`define SPEC_{instr.upper()} {int(instr in self.instrs)}" for instr in INSTRS],
            "",
            "`endif"
        ])

    def add_jmps(self):
        self.add("RISCV_JAL", "RISCV_JALR")

    def add_itype(self):
        self.add("ITYPE")
        self.add("SHIFTIOP")

    def add_rtype(self):
        self.add("RTYPE")

    def add_fences(self):
        self.add("FENCE", "FENCEI")

    def add_loads(self):
        self.add("LOAD")

    def add_stores(self):
        self.add("STORE")

    def add_mtypes(self):
        self.add("MUL", "DIV", "REM")

    def add_illegal(self, extra=True):
        self.add("ILLEGAL", "C_ILLEGAL")
        if extra:
            self.add("CSR")
            self.add("MRET", "WFI")

    def add_system(self):
        self.add("ECALL", "EBREAK", "MRET", "WFI")

    def add_csr(self):
        self.add("CSR")

    def add_utypes(self):
        self.add("UTYPE")

    def add_btypes(self):
        self.add("BTYPE")

conf = SpecConfig()
conf.add_noncompressed()

if len(sys.argv) > 1:
    if sys.argv[1] == "unreachables":
        print(conf.make_sail_unreachables())
    elif sys.argv[1] == "header":
        print(conf.make_sv_header())
    elif sys.argv[1] == "unreachable_loc_hack":
        with open("build/ibexspec.sv", "r") as f:
            c = f.read()
        c = c.replace(
            "sail_reached_unreachable = 1;",
            "begin sail_reached_unreachable = 1; sail_reached_unreachable_loc = `__LINE__; end"
        ).replace(
            "sail_reached_unreachable = 0;",
            "begin sail_reached_unreachable = 0; sail_reached_unreachable_loc = -1; end"
        ).replace(
            "bit sail_reached_unreachable;",
            "bit sail_reached_unreachable;\n\tlogic [31:0] sail_reached_unreachable_loc;"
        )
        with open("build/ibexspec.sv", "w") as f:
            f.write(c)
else:
    print("Intended usage is to run make sv")
