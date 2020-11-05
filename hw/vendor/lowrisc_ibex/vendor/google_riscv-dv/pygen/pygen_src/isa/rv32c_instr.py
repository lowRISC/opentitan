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

from pygen_src.riscv_defines import DEFINE_C_INSTR
from pygen_src.riscv_instr_pkg import (riscv_instr_name_t, riscv_instr_format_t,
                                       riscv_instr_category_t, riscv_instr_group_t, imm_t)


DEFINE_C_INSTR(riscv_instr_name_t.C_LW, riscv_instr_format_t.CL_FORMAT,
               riscv_instr_category_t.LOAD, riscv_instr_group_t.RV32C, imm_t.UIMM, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_SW, riscv_instr_format_t.CS_FORMAT,
               riscv_instr_category_t.STORE, riscv_instr_group_t.RV32C, imm_t.UIMM, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_LWSP, riscv_instr_format_t.CI_FORMAT,
               riscv_instr_category_t.LOAD, riscv_instr_group_t.RV32C, imm_t.UIMM, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_SWSP, riscv_instr_format_t.CSS_FORMAT,
               riscv_instr_category_t.STORE, riscv_instr_group_t.RV32C, imm_t.UIMM, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_ADDI4SPN, riscv_instr_format_t.CIW_FORMAT,
               riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32C, imm_t.NZUIMM,
               g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_ADDI, riscv_instr_format_t.CI_FORMAT,
               riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32C, imm_t.NZIMM,
               g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_ADDI16SP, riscv_instr_format_t.CI_FORMAT,
               riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32C, imm_t.NZIMM,
               g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_LI, riscv_instr_format_t.CI_FORMAT,
               riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_LUI, riscv_instr_format_t.CI_FORMAT,
               riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32C, imm_t.NZIMM,
               g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_SUB, riscv_instr_format_t.CA_FORMAT,
               riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_ADD, riscv_instr_format_t.CR_FORMAT,
               riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_NOP, riscv_instr_format_t.CI_FORMAT,
               riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_MV, riscv_instr_format_t.CR_FORMAT,
               riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_ANDI, riscv_instr_format_t.CB_FORMAT,
               riscv_instr_category_t.LOGICAL, riscv_instr_group_t.RV32C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_XOR, riscv_instr_format_t.CA_FORMAT,
               riscv_instr_category_t.LOGICAL, riscv_instr_group_t.RV32C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_OR, riscv_instr_format_t.CA_FORMAT,
               riscv_instr_category_t.LOGICAL, riscv_instr_group_t.RV32C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_AND, riscv_instr_format_t.CA_FORMAT,
               riscv_instr_category_t.LOGICAL, riscv_instr_group_t.RV32C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_BEQZ, riscv_instr_format_t.CB_FORMAT,
               riscv_instr_category_t.BRANCH, riscv_instr_group_t.RV32C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_BNEZ, riscv_instr_format_t.CB_FORMAT,
               riscv_instr_category_t.BRANCH, riscv_instr_group_t.RV32C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_SRLI, riscv_instr_format_t.CB_FORMAT,
               riscv_instr_category_t.SHIFT, riscv_instr_group_t.RV32C, imm_t.NZUIMM, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_SRAI, riscv_instr_format_t.CB_FORMAT,
               riscv_instr_category_t.SHIFT, riscv_instr_group_t.RV32C, imm_t.NZUIMM, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_SLLI, riscv_instr_format_t.CI_FORMAT,
               riscv_instr_category_t.SHIFT, riscv_instr_group_t.RV32C, imm_t.NZUIMM, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_J, riscv_instr_format_t.CJ_FORMAT,
               riscv_instr_category_t.JUMP, riscv_instr_group_t.RV32C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_JAL, riscv_instr_format_t.CJ_FORMAT,
               riscv_instr_category_t.JUMP, riscv_instr_group_t.RV32C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_JR, riscv_instr_format_t.CR_FORMAT,
               riscv_instr_category_t.JUMP, riscv_instr_group_t.RV32C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_JALR, riscv_instr_format_t.CR_FORMAT,
               riscv_instr_category_t.JUMP, riscv_instr_group_t.RV32C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_EBREAK, riscv_instr_format_t.CI_FORMAT,
               riscv_instr_category_t.SYSTEM, riscv_instr_group_t.RV32C, g=globals())
