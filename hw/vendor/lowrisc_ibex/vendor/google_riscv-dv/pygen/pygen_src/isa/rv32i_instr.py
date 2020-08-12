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

from pygen_src.riscv_defines import DEFINE_INSTR
from pygen_src.riscv_instr_pkg import (riscv_instr_name_t, riscv_instr_format_t,
                                       riscv_instr_category_t, riscv_instr_group_t, imm_t)


# LOAD instructions
DEFINE_INSTR(riscv_instr_name_t.LB, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.LOAD, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.LH, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.LOAD, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.LW, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.LOAD, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.LBU, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.LOAD, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.LHU, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.LOAD, riscv_instr_group_t.RV32I, g=globals())
# STORE instructions
DEFINE_INSTR(riscv_instr_name_t.SB, riscv_instr_format_t.S_FORMAT,
             riscv_instr_category_t.STORE, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SH, riscv_instr_format_t.S_FORMAT,
             riscv_instr_category_t.STORE, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SW, riscv_instr_format_t.S_FORMAT,
             riscv_instr_category_t.STORE, riscv_instr_group_t.RV32I, g=globals())
# SHIFT intructions
DEFINE_INSTR(riscv_instr_name_t.SLL, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.SHIFT, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SLLI, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.SHIFT, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SRL, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.SHIFT, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SRLI, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.SHIFT, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SRA, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.SHIFT, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SRAI, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.SHIFT, riscv_instr_group_t.RV32I, g=globals())
# ARITHMETIC intructions
DEFINE_INSTR(riscv_instr_name_t.ADD, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.ADDI, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.NOP, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SUB, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.LUI, riscv_instr_format_t.U_FORMAT,
             riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32I, imm_t.UIMM, g=globals())
DEFINE_INSTR(riscv_instr_name_t.AUIPC, riscv_instr_format_t.U_FORMAT,
             riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32I, imm_t.UIMM, g=globals())
# LOGICAL instructions
DEFINE_INSTR(riscv_instr_name_t.XOR, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.LOGICAL, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.XORI, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.LOGICAL, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.OR, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.LOGICAL, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.ORI, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.LOGICAL, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.AND, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.LOGICAL, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.ANDI, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.LOGICAL, riscv_instr_group_t.RV32I, g=globals())
# COMPARE instructions
DEFINE_INSTR(riscv_instr_name_t.SLT, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.COMPARE, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SLTI, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.COMPARE, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SLTU, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.COMPARE, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SLTIU, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.COMPARE, riscv_instr_group_t.RV32I, g=globals())
# BRANCH instructions
DEFINE_INSTR(riscv_instr_name_t.BEQ, riscv_instr_format_t.B_FORMAT,
             riscv_instr_category_t.BRANCH, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.BNE, riscv_instr_format_t.B_FORMAT,
             riscv_instr_category_t.BRANCH, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.BLT, riscv_instr_format_t.B_FORMAT,
             riscv_instr_category_t.BRANCH, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.BGE, riscv_instr_format_t.B_FORMAT,
             riscv_instr_category_t.BRANCH, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.BLTU, riscv_instr_format_t.B_FORMAT,
             riscv_instr_category_t.BRANCH, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.BGEU, riscv_instr_format_t.B_FORMAT,
             riscv_instr_category_t.BRANCH, riscv_instr_group_t.RV32I, g=globals())
# JUMP instructions
DEFINE_INSTR(riscv_instr_name_t.JAL, riscv_instr_format_t.J_FORMAT,
             riscv_instr_category_t.JUMP, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.JALR, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.JUMP, riscv_instr_group_t.RV32I, g=globals())
# SYNCH instructions
DEFINE_INSTR(riscv_instr_name_t.FENCE, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.SYNCH, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.FENCE_I, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.SYNCH, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SFENCE_VMA, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.SYNCH, riscv_instr_group_t.RV32I, g=globals())
# SYSTEM instructions
DEFINE_INSTR(riscv_instr_name_t.ECALL, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.SYSTEM, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.EBREAK, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.SYSTEM, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.URET, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.SYSTEM, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SRET, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.SYSTEM, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.MRET, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.SYSTEM, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.DRET, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.SYSTEM, riscv_instr_group_t.RV32I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.WFI, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.INTERRUPT, riscv_instr_group_t.RV32I, g=globals())
# CSR instructions
DEFINE_INSTR(riscv_instr_name_t.CSRRW, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.CSR, riscv_instr_group_t.RV32I, imm_t.UIMM, g=globals())
DEFINE_INSTR(riscv_instr_name_t.CSRRS, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.CSR, riscv_instr_group_t.RV32I, imm_t.UIMM, g=globals())
DEFINE_INSTR(riscv_instr_name_t.CSRRC, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.CSR, riscv_instr_group_t.RV32I, imm_t.UIMM, g=globals())
DEFINE_INSTR(riscv_instr_name_t.CSRRWI, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.CSR, riscv_instr_group_t.RV32I, imm_t.UIMM, g=globals())
DEFINE_INSTR(riscv_instr_name_t.CSRRSI, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.CSR, riscv_instr_group_t.RV32I, imm_t.UIMM, g=globals())
DEFINE_INSTR(riscv_instr_name_t.CSRRCI, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.CSR, riscv_instr_group_t.RV32I, imm_t.UIMM, g=globals())
