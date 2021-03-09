"""
Copyright 2020 Google LLC
Copyright 2020 PerfectVIPs Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
"""

import sys
import logging
import vsc
from pygen_src.isa.riscv_instr import riscv_instr
from pygen_src.riscv_instr_pkg import pkg_ins, riscv_instr_name_t, riscv_instr_group_t


@vsc.randobj
class riscv_amo_instr(riscv_instr):
    def __init__(self):
        super().__init__()
        self.aq = vsc.rand_bit_t(1)
        self.rl = vsc.rand_bit_t(1)

    @vsc.constraint
    def aq_rl_c(self):
        self.aq & self.rl == 0

    def get_instr_name(self):
        get_instr_name = self.instr_name.name
        if self.group == riscv_instr_group_t.RV32A:
            get_instr_name = "{}.w".format(get_instr_name[:-2])
            if self.aq:
                get_instr_name = "{}.aq".format(get_instr_name)
            else:
                if self.rl:
                    get_instr_name = "{}.rl".format(get_instr_name)
                else:
                    get_instr_name = get_instr_name
        elif self.group == riscv_instr_group_t.RV64A:
            get_instr_name = "{}.d".format(get_instr_name[:-2])
            if self.aq:
                get_instr_name = "{}.aq".format(get_instr_name)
            else:
                if self.rl:
                    get_instr_name = "{}.rl".format(get_instr_name)
        else:
            logging.critical("Unexpected amo instr group: {} / {}"
                             .format(self.group.name, self.instr_name.name))
            sys.exit(1)
        return get_instr_name

    # Convert the instruction to assembly code
    def convert2asm(self, prefix = ""):
        asm_str = pkg_ins.format_string(self.get_instr_name(), pkg_ins.MAX_INSTR_STR_LEN)
        if self.group in [riscv_instr_group_t.RV32A, riscv_instr_group_t.RV64A]:
            if self.instr_name in [riscv_instr_name_t.LR_W, riscv_instr_name_t.LR_D]:
                asm_str = "{} {}, ({})".format(asm_str, self.rd.name, self.rs1.name)
            else:
                asm_str = "{} {}, {}, ({})".format(asm_str, self.rd.name, self.rs2.name,
                                                   self.rs1.name)
        else:
            logging.critical("Unexpected amo instr group: {} / {}"
                             .format(self.group.name, self.instr_name.name))
            sys.exit(1)
        if self.comment != "":
            asm_str = "{} #{}".format(asm_str, self.comment)
        return asm_str.lower()
