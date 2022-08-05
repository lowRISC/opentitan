/*
 * Copyright 2020 Google LLC
 * Copyright 2022 Coverify Systems Technology
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

module riscv.gen.isa.rv32c_instr;

import riscv.gen.riscv_defines;

import uvm;

version (RISCV_INSTR_STRING_MIXIN) {
  mixin (riscv_c_instr_mixin(C_LW,       CL_FORMAT, LOAD, RV32C, UIMM));
  mixin (riscv_c_instr_mixin(C_SW,       CS_FORMAT, STORE, RV32C, UIMM));
  mixin (riscv_c_instr_mixin(C_LWSP,     CI_FORMAT, LOAD, RV32C, UIMM));
  mixin (riscv_c_instr_mixin(C_SWSP,     CSS_FORMAT, STORE, RV32C, UIMM));
  mixin (riscv_c_instr_mixin(C_ADDI4SPN, CIW_FORMAT, ARITHMETIC, RV32C, NZUIMM));
  mixin (riscv_c_instr_mixin(C_ADDI,     CI_FORMAT, ARITHMETIC, RV32C, NZIMM));
  mixin (riscv_c_instr_mixin(C_ADDI16SP, CI_FORMAT, ARITHMETIC, RV32C, NZIMM));
  mixin (riscv_c_instr_mixin(C_LI,       CI_FORMAT, ARITHMETIC, RV32C));
  mixin (riscv_c_instr_mixin(C_LUI,      CI_FORMAT, ARITHMETIC, RV32C, NZIMM));
  mixin (riscv_c_instr_mixin(C_SUB,      CA_FORMAT, ARITHMETIC, RV32C));
  mixin (riscv_c_instr_mixin(C_ADD,      CR_FORMAT, ARITHMETIC, RV32C));
  mixin (riscv_c_instr_mixin(C_NOP,      CI_FORMAT, ARITHMETIC, RV32C));
  mixin (riscv_c_instr_mixin(C_MV,       CR_FORMAT, ARITHMETIC, RV32C));
  mixin (riscv_c_instr_mixin(C_ANDI,     CB_FORMAT, LOGICAL, RV32C));
  mixin (riscv_c_instr_mixin(C_XOR,      CA_FORMAT, LOGICAL, RV32C));
  mixin (riscv_c_instr_mixin(C_OR,       CA_FORMAT, LOGICAL, RV32C));
  mixin (riscv_c_instr_mixin(C_AND,      CA_FORMAT, LOGICAL, RV32C));
  mixin (riscv_c_instr_mixin(C_BEQZ,     CB_FORMAT, BRANCH, RV32C));
  mixin (riscv_c_instr_mixin(C_BNEZ,     CB_FORMAT, BRANCH, RV32C));
  mixin (riscv_c_instr_mixin(C_SRLI,     CB_FORMAT, SHIFT, RV32C, NZUIMM));
  mixin (riscv_c_instr_mixin(C_SRAI,     CB_FORMAT, SHIFT, RV32C, NZUIMM));
  mixin (riscv_c_instr_mixin(C_SLLI,     CI_FORMAT, SHIFT, RV32C, NZUIMM));
  mixin (riscv_c_instr_mixin(C_J,        CJ_FORMAT, JUMP, RV32C));
  mixin (riscv_c_instr_mixin(C_JAL,      CJ_FORMAT, JUMP, RV32C));
  mixin (riscv_c_instr_mixin(C_JR,       CR_FORMAT, JUMP, RV32C));
  mixin (riscv_c_instr_mixin(C_JALR,     CR_FORMAT, JUMP, RV32C));
  mixin (riscv_c_instr_mixin(C_EBREAK,   CI_FORMAT, SYSTEM, RV32C));
 }
 else {
   class riscv_C_LW_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_LW,       CL_FORMAT, LOAD, RV32C, UIMM); }
   class riscv_C_SW_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_SW,       CS_FORMAT, STORE, RV32C, UIMM); }
   class riscv_C_LWSP_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_LWSP,     CI_FORMAT, LOAD, RV32C, UIMM); }
   class riscv_C_SWSP_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_SWSP,     CSS_FORMAT, STORE, RV32C, UIMM); }
   class riscv_C_ADDI4SPN_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_ADDI4SPN, CIW_FORMAT, ARITHMETIC, RV32C, NZUIMM); }
   class riscv_C_ADDI_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_ADDI,     CI_FORMAT, ARITHMETIC, RV32C, NZIMM); }
   class riscv_C_ADDI16SP_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_ADDI16SP, CI_FORMAT, ARITHMETIC, RV32C, NZIMM); }
   class riscv_C_LI_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_LI,       CI_FORMAT, ARITHMETIC, RV32C); }
   class riscv_C_LUI_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_LUI,      CI_FORMAT, ARITHMETIC, RV32C, NZIMM); }
   class riscv_C_SUB_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_SUB,      CA_FORMAT, ARITHMETIC, RV32C); }
   class riscv_C_ADD_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_ADD,      CR_FORMAT, ARITHMETIC, RV32C); }
   class riscv_C_NOP_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_NOP,      CI_FORMAT, ARITHMETIC, RV32C); }
   class riscv_C_MV_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_MV,       CR_FORMAT, ARITHMETIC, RV32C); }
   class riscv_C_ANDI_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_ANDI,     CB_FORMAT, LOGICAL, RV32C); }
   class riscv_C_XOR_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_XOR,      CA_FORMAT, LOGICAL, RV32C); }
   class riscv_C_OR_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_OR,       CA_FORMAT, LOGICAL, RV32C); }
   class riscv_C_AND_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_AND,      CA_FORMAT, LOGICAL, RV32C); }
   class riscv_C_BEQZ_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_BEQZ,     CB_FORMAT, BRANCH, RV32C); }
   class riscv_C_BNEZ_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_BNEZ,     CB_FORMAT, BRANCH, RV32C); }
   class riscv_C_SRLI_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_SRLI,     CB_FORMAT, SHIFT, RV32C, NZUIMM); }
   class riscv_C_SRAI_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_SRAI,     CB_FORMAT, SHIFT, RV32C, NZUIMM); }
   class riscv_C_SLLI_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_SLLI,     CI_FORMAT, SHIFT, RV32C, NZUIMM); }
   class riscv_C_J_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_J,        CJ_FORMAT, JUMP, RV32C); }
   class riscv_C_JAL_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_JAL,      CJ_FORMAT, JUMP, RV32C); }
   class riscv_C_JR_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_JR,       CR_FORMAT, JUMP, RV32C); }
   class riscv_C_JALR_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_JALR,     CR_FORMAT, JUMP, RV32C); }
   class riscv_C_EBREAK_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_EBREAK,   CI_FORMAT, SYSTEM, RV32C); }
 }
