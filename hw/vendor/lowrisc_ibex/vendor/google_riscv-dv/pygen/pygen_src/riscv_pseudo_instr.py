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

import vsc
from pygen_src.isa.riscv_instr import riscv_instr
from pygen_src.riscv_instr_pkg import (riscv_pseudo_instr_name_t, riscv_instr_format_t,
                                       riscv_instr_category_t, riscv_instr_group_t, pkg_ins)
# from pygen_src.riscv_defines import add_pseudo_instr


# Psuedo instructions are used to simplify assembly program writing
@vsc.randobj
class riscv_pseudo_instr(riscv_instr):
    def __init__(self):
        super().__init__()
        self.process_load_store = 0
        self.format = riscv_instr_format_t.I_FORMAT
        self.pseudo_instr_name = vsc.rand_enum_t(riscv_pseudo_instr_name_t)

    '''
    TODO
    add_pseudo_instr(self, riscv_pseudo_instr_name_t.LI, riscv_instr_format_t.I_FORMAT,
                     riscv_instr_category_t.LOAD, riscv_instr_group_t.RV32I)
    add_pseudo_instr(self, riscv_pseudo_instr_name_t.LA, riscv_instr_format_t.I_FORMAT,
                     riscv_instr_category_t.LOAD, riscv_instr_group_t.RV32I)
    '''

    # Convert the instruction to assembly code
    def convert2asm(self, prefix = ""):
        asm_str = pkg_ins.format_string(self.get_instr_name(), pkg_ins.MAX_INSTR_STR_LEN)
        # instr rd,imm
        asm_str = "{}{}, {}".format(asm_str, self.rd.name, self.get_imm())
        if self.comment != "":
            asm_str = "{} #{}".format(asm_str, self.comment)
        return asm_str.lower()

    def get_instr_name(self):
        return self.pseudo_instr_name.name
