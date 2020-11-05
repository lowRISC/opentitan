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

import logging
import vsc
from pygen_src.isa.riscv_instr import riscv_instr
from pygen_src.riscv_instr_pkg import (riscv_instr_name_t, riscv_instr_format_t,
                                       riscv_instr_category_t, riscv_reg_t, imm_t, pkg_ins)


@vsc.randobj
class riscv_compressed_instr(riscv_instr):
    def __init__(self):
        super().__init__()
        self.imm_align = 0
        self.rs1 = riscv_reg_t.S0
        self.rs2 = riscv_reg_t.S0
        self.rd = riscv_reg_t.S0
        self.is_compressed = 1

    @vsc.constraint
    def rvc_csr_c(self):
        # Registers specified by the three-bit rs1’, rs2’, and rd’
        with vsc.implies(self.format.inside(vsc.rangelist(riscv_instr_format_t.CIW_FORMAT,
                                                          riscv_instr_format_t.CL_FORMAT,
                                                          riscv_instr_format_t.CS_FORMAT,
                                                          riscv_instr_format_t.CB_FORMAT,
                                                          riscv_instr_format_t.CA_FORMAT))):
            with vsc.implies(self.has_rs1 == 1):
                self.rs1.inside(vsc.rangelist(riscv_reg_t.S0, riscv_reg_t.S1, riscv_reg_t.A0,
                                              riscv_reg_t.A1, riscv_reg_t.A2, riscv_reg_t.A3,
                                              riscv_reg_t.A4, riscv_reg_t.A5))
            with vsc.implies(self.has_rs2 == 1):
                self.rs2.inside(vsc.rangelist(riscv_reg_t.S0, riscv_reg_t.S1, riscv_reg_t.A0,
                                              riscv_reg_t.A1, riscv_reg_t.A2, riscv_reg_t.A3,
                                              riscv_reg_t.A4, riscv_reg_t.A5))
            with vsc.implies(self.has_rd == 1):
                self.rd.inside(vsc.rangelist(riscv_reg_t.S0, riscv_reg_t.S1, riscv_reg_t.A0,
                                             riscv_reg_t.A1, riscv_reg_t.A2, riscv_reg_t.A3,
                                             riscv_reg_t.A4, riscv_reg_t.A5))
        # _ADDI16SP is only valid when rd == SP
        with vsc.implies(self.instr_name == riscv_instr_name_t.C_ADDI16SP):
            self.rd == riscv_reg_t.SP
        with vsc.implies(self.instr_name.inside(vsc.rangelist(riscv_instr_name_t.C_JR,
                                                              riscv_instr_name_t.C_JALR))):
            self.rs1 != riscv_reg_t.ZERO
            self.rs2 == riscv_reg_t.ZERO

    @vsc.constraint
    def imm_val_c(self):
        with vsc.implies(self.imm_type.inside(vsc.rangelist(imm_t.NZIMM, imm_t.NZUIMM))):
            self.imm[5:0] != 0
            with vsc.implies(self.instr_name == riscv_instr_name_t.C_LUI):
                self.imm[31:5] == 0
            with vsc.implies(self.instr_name.inside(vsc.rangelist(riscv_instr_name_t.C_SRAI,
                                                                  riscv_instr_name_t.C_SRLI,
                                                                  riscv_instr_name_t.C_SLLI))):
                self.imm[31:5] == 0
            with vsc.implies(self.instr_name == riscv_instr_name_t.C_ADDI4SPN):
                self.imm[1:0] == 0

    # C_JAL is RV32C only instruction
    @vsc.constraint
    def jal_c(self):
        with vsc.implies(self.XLEN != 32):
            self.instr_name != riscv_instr_name_t.C_JAL

    # Avoid generating HINT or illegal instruction by default as it's not supported by the compiler
    @vsc.constraint
    def no_hint_illegal_instr_c(self):
        with vsc.implies(self.instr_name.inside(vsc.rangelist(riscv_instr_name_t.C_ADDI,
                                                              riscv_instr_name_t.C_ADDIW,
                                                              riscv_instr_name_t.C_LI,
                                                              riscv_instr_name_t.C_LUI,
                                                              riscv_instr_name_t.C_SLLI,
                                                              riscv_instr_name_t.C_SLLI64,
                                                              riscv_instr_name_t.C_LQSP,
                                                              riscv_instr_name_t.C_LDSP,
                                                              riscv_instr_name_t.C_MV,
                                                              riscv_instr_name_t.C_ADD,
                                                              riscv_instr_name_t.C_LWSP))):
            self.rd != riscv_reg_t.ZERO
        with vsc.implies(self.instr_name == riscv_instr_name_t.C_JR):
            self.rs1 != riscv_reg_t.ZERO
        with vsc.implies(self.instr_name.inside(vsc.rangelist(riscv_instr_name_t.C_ADD,
                                                              riscv_instr_name_t.C_MV))):
            self.rs2 != riscv_reg_t.ZERO
        with vsc.implies(self.instr_name == riscv_instr_name_t.C_LUI):
            self.rd != riscv_reg_t.SP

    def set_imm_len(self):
        if self.format in [riscv_instr_format_t.CI_FORMAT, riscv_instr_format_t.CSS_FORMAT]:
            self.imm_len = 6
        elif self.format in [riscv_instr_format_t.CL_FORMAT, riscv_instr_format_t.CS_FORMAT]:
            self.imm_len = 5
        elif self.format in [riscv_instr_format_t.CJ_FORMAT]:
            self.imm_len = 11
        elif self.format in [riscv_instr_format_t.CB_FORMAT]:
            if self.instr_name == riscv_instr_name_t.C_ANDI:
                self.imm_len = 6
            else:
                self.imm_len = 7
        elif self.format in [riscv_instr_format_t.CB_FORMAT, riscv_instr_format_t.CIW_FORMAT]:
            self.imm_len = 8
        if self.instr_name in [riscv_instr_name_t.C_SQ, riscv_instr_name_t.C_LQ,
                               riscv_instr_name_t.C_LQSP, riscv_instr_name_t.C_SQSP,
                               riscv_instr_name_t.C_ADDI16SP]:
            self.imm_align = 4
        elif self.instr_name in [riscv_instr_name_t.C_SD, riscv_instr_name_t.C_LD,
                                 riscv_instr_name_t.C_LDSP, riscv_instr_name_t.C_SDSP]:
            self.imm_align = 3
        elif self.instr_name in [riscv_instr_name_t.C_SW, riscv_instr_name_t.C_LW,
                                 riscv_instr_name_t.C_LWSP, riscv_instr_name_t.C_SWSP,
                                 riscv_instr_name_t.C_ADDI4SPN]:
            self.imm_align = 2
        elif self.instr_name in [riscv_instr_name_t.C_LUI]:
            self.imm_align = 12
        elif self.instr_name in [riscv_instr_name_t.C_J, riscv_instr_name_t.C_JAL,
                                 riscv_instr_name_t.C_BNEZ, riscv_instr_name_t.C_BEQZ]:
            self.imm_align = 1

    def extend_imm(self):
        if self.instr_name != riscv_instr_name_t.C_LUI:
            super().extend_imm()
            self.imm = self.imm << self.imm_align

    def set_rand_mode(self):
        if self.format in [riscv_instr_format_t.CR_FORMAT]:
            if self.category in [riscv_instr_category_t.JUMP]:
                self.has_rd = 0
            else:
                self.has_rs1 = 0
            self.has_imm = 0
        elif self.format in [riscv_instr_format_t.CI_FORMAT, riscv_instr_format_t.CIW_FORMAT]:
            self.has_rs2 = 0
            self.has_rs1 = 0
        elif self.format in [riscv_instr_format_t.CSS_FORMAT]:
            self.has_rs1 = 0
            self.has_rd = 0
        elif self.format in [riscv_instr_format_t.CL_FORMAT]:
            self.has_rs2 = 0
        elif self.format in [riscv_instr_format_t.CS_FORMAT]:
            self.has_rd = 0
        elif self.format in [riscv_instr_format_t.CA_FORMAT]:
            self.has_rs1 = 0
            self.has_imm = 0
        elif self.format == riscv_instr_format_t.CJ_FORMAT:
            self.has_rs1 = 0
            self.has_rs2 = 0
            self.has_rd = 0
        elif self.format == riscv_instr_format_t.CB_FORMAT:
            if self.instr_name != riscv_instr_name_t.C_ANDI:
                self.has_rd = 0
            self.has_rs2 = 0

    def convert2asm(self, prefix=""):
        asm_str = pkg_ins.format_string(string=self.get_instr_name(),
                                        length=pkg_ins.MAX_INSTR_STR_LEN)
        if self.category != riscv_instr_category_t.SYSTEM:
            if self.format in [riscv_instr_format_t.CI_FORMAT, riscv_instr_format_t.CIW_FORMAT]:
                if self.instr_name is riscv_instr_name_t.C_NOP:
                    asm_str = "c.nop"
                elif self.instr_name is riscv_instr_name_t.C_ADDI16SP:
                    asm_str = "{} sp, {}".format(asm_str, self.get_imm())
                elif self.instr_name is riscv_instr_name_t.C_ADDI4SPN:
                    asm_str = "{} {}, sp, {}".format(asm_str, self.rd.name, self.get_imm())
                elif self.instr_name in [riscv_instr_name_t.C_LDSP, riscv_instr_name_t.C_LWSP,
                                         riscv_instr_name_t.C_LQSP]:
                    asm_str = "{} {}, {}(sp)".format(asm_str, self.rd.name, self.get_imm())
                else:
                    asm_str = "{} {}, {}".format(asm_str, self.rd.name, self.get_imm())
            elif self.format is riscv_instr_format_t.CL_FORMAT:
                asm_str = "{} {}, {}({})".format(
                    asm_str, self.rd.name, self.get_imm(), self.rs1.name)
            elif self.format is riscv_instr_format_t.CS_FORMAT:
                if self.category is riscv_instr_category_t.STORE:
                    asm_str = "{} {}, {}({})".format(
                        asm_str, self.rs2.name, self.get_imm(), self.rs1.name)
                else:
                    asm_str = "{} {}, {}".format(asm_str, self.rs1.name, self.rs2.name)
            elif self.format is riscv_instr_format_t.CA_FORMAT:
                asm_str = "{} {}, {}".format(asm_str, self.rd.name, self.rs2.name)
            elif self.format is riscv_instr_format_t.CB_FORMAT:
                asm_str = "{} {}, {}".format(asm_str, self.rs1.name, self.get_imm())
            elif self.format is riscv_instr_format_t.CSS_FORMAT:
                if self.category is riscv_instr_category_t.STORE:
                    asm_str = "{} {}, {}(sp)".format(asm_str, self.rs2.name, self.get_imm())
                else:
                    asm_str = "{} {}, {}".format(asm_str, self.rs2.name, self.get_imm())
            elif self.format is riscv_instr_format_t.CR_FORMAT:
                if self.instr_name in [riscv_instr_name_t.C_JR, riscv_instr_name_t.C_JALR]:
                    asm_str = "{} {}".format(asm_str, self.rs1.name)
                else:
                    asm_str = "{} {}, {}".format(asm_str, self.rd.name, self.rs2.name)
            elif self.format is riscv_instr_format_t.CJ_FORMAT:
                asm_str = "{} {}".format(asm_str, self.get_imm())
            else:
                logging.info("Unsupported format {}".format(self.format.name))
        else:
            # For EBREAK,C.EBREAK, making sure pc+4 is a valid instruction boundary
            # This is needed to resume execution from epc+4 after ebreak handling
            if self.instr_name is riscv_instr_name_t.C_EBREAK:
                asm_str = "c.ebreak;c.nop;"
            if self.comment != "":
                asm_str = asm_str + " #" + self.comment
        return asm_str.lower()

    # TODO
    def conver2bin(self, prefix=""):
        pass

    # TODO
    def get_c_opcode(self):
        pass

    # TOD0
    def get_func3(self):
        pass
