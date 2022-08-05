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
module riscv.gen.isa.rv32i_instr;

import riscv.gen.riscv_defines;

import uvm;


version (RISCV_INSTR_STRING_MIXIN) {
  // LOAD instructions
  mixin (riscv_instr_mixin(LB,     I_FORMAT, LOAD, RV32I));
  mixin (riscv_instr_mixin(LH,     I_FORMAT, LOAD, RV32I));
  mixin (riscv_instr_mixin(LW,     I_FORMAT, LOAD, RV32I));
  mixin (riscv_instr_mixin(LBU,    I_FORMAT, LOAD, RV32I));
  mixin (riscv_instr_mixin(LHU,    I_FORMAT, LOAD, RV32I));
  // STORE instructions
  mixin (riscv_instr_mixin(SB,     S_FORMAT, STORE, RV32I));
  mixin (riscv_instr_mixin(SH,     S_FORMAT, STORE, RV32I));
  mixin (riscv_instr_mixin(SW,     S_FORMAT, STORE, RV32I));
  // SHIFT intructions
  mixin (riscv_instr_mixin(SLL,    R_FORMAT, SHIFT, RV32I));
  mixin (riscv_instr_mixin(SLLI,   I_FORMAT, SHIFT, RV32I));
  mixin (riscv_instr_mixin(SRL,    R_FORMAT, SHIFT, RV32I));
  mixin (riscv_instr_mixin(SRLI,   I_FORMAT, SHIFT, RV32I));
  mixin (riscv_instr_mixin(SRA,    R_FORMAT, SHIFT, RV32I));
  mixin (riscv_instr_mixin(SRAI,   I_FORMAT, SHIFT, RV32I));
  // ARITHMETIC intructions
  mixin (riscv_instr_mixin(ADD,    R_FORMAT, ARITHMETIC, RV32I));
  mixin (riscv_instr_mixin(ADDI,   I_FORMAT, ARITHMETIC, RV32I));
  mixin (riscv_instr_mixin(NOP,    I_FORMAT, ARITHMETIC, RV32I));
  mixin (riscv_instr_mixin(SUB,    R_FORMAT, ARITHMETIC, RV32I));
  mixin (riscv_instr_mixin(LUI,    U_FORMAT, ARITHMETIC, RV32I, UIMM));
  mixin (riscv_instr_mixin(AUIPC,  U_FORMAT, ARITHMETIC, RV32I, UIMM));
  // LOGICAL instructions
  mixin (riscv_instr_mixin(XOR,    R_FORMAT, LOGICAL, RV32I));
  mixin (riscv_instr_mixin(XORI,   I_FORMAT, LOGICAL, RV32I));
  mixin (riscv_instr_mixin(OR,     R_FORMAT, LOGICAL, RV32I));
  mixin (riscv_instr_mixin(ORI,    I_FORMAT, LOGICAL, RV32I));
  mixin (riscv_instr_mixin(AND,    R_FORMAT, LOGICAL, RV32I));
  mixin (riscv_instr_mixin(ANDI,   I_FORMAT, LOGICAL, RV32I));
  // COMPARE instructions
  mixin (riscv_instr_mixin(SLT,    R_FORMAT, COMPARE, RV32I));
  mixin (riscv_instr_mixin(SLTI,   I_FORMAT, COMPARE, RV32I));
  mixin (riscv_instr_mixin(SLTU,   R_FORMAT, COMPARE, RV32I));
  mixin (riscv_instr_mixin(SLTIU,  I_FORMAT, COMPARE, RV32I));
  // BRANCH instructions
  mixin (riscv_instr_mixin(BEQ,    B_FORMAT, BRANCH, RV32I));
  mixin (riscv_instr_mixin(BNE,    B_FORMAT, BRANCH, RV32I));
  mixin (riscv_instr_mixin(BLT,    B_FORMAT, BRANCH, RV32I));
  mixin (riscv_instr_mixin(BGE,    B_FORMAT, BRANCH, RV32I));
  mixin (riscv_instr_mixin(BLTU,   B_FORMAT, BRANCH, RV32I));
  mixin (riscv_instr_mixin(BGEU,   B_FORMAT, BRANCH, RV32I));
  // JUMP instructions
  mixin (riscv_instr_mixin(JAL,    J_FORMAT, JUMP, RV32I));
  mixin (riscv_instr_mixin(JALR,   I_FORMAT, JUMP, RV32I));
  // SYNCH instructions
  mixin (riscv_instr_mixin(FENCE,  I_FORMAT, SYNCH, RV32I));
  mixin (riscv_instr_mixin(FENCE_I, I_FORMAT, SYNCH, RV32I));
  mixin (riscv_instr_mixin(SFENCE_VMA, R_FORMAT, SYNCH, RV32I));
  // SYSTEM instructions
  mixin (riscv_instr_mixin(ECALL,   I_FORMAT, SYSTEM, RV32I));
  mixin (riscv_instr_mixin(EBREAK,  I_FORMAT, SYSTEM, RV32I));
  mixin (riscv_instr_mixin(URET,    I_FORMAT, SYSTEM, RV32I));
  mixin (riscv_instr_mixin(SRET,    I_FORMAT, SYSTEM, RV32I));
  mixin (riscv_instr_mixin(MRET,    I_FORMAT, SYSTEM, RV32I));
  mixin (riscv_instr_mixin(DRET,    I_FORMAT, SYSTEM, RV32I));
  mixin (riscv_instr_mixin(WFI,     I_FORMAT, INTERRUPT, RV32I));
  // CSR instructions
  mixin (riscv_instr_mixin(CSRRW,  R_FORMAT, CSR, RV32I, UIMM));
  mixin (riscv_instr_mixin(CSRRS,  R_FORMAT, CSR, RV32I, UIMM));
  mixin (riscv_instr_mixin(CSRRC,  R_FORMAT, CSR, RV32I, UIMM));
  mixin (riscv_instr_mixin(CSRRWI, I_FORMAT, CSR, RV32I, UIMM));
  mixin (riscv_instr_mixin(CSRRSI, I_FORMAT, CSR, RV32I, UIMM));
  mixin (riscv_instr_mixin(CSRRCI, I_FORMAT, CSR, RV32I, UIMM));
 }
 else {
   // LOAD instructions
   class riscv_LB_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(LB,     I_FORMAT, LOAD, RV32I); }
   class riscv_LH_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(LH,     I_FORMAT, LOAD, RV32I); }
   class riscv_LW_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(LW,     I_FORMAT, LOAD, RV32I); }
   class riscv_LBU_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(LBU,    I_FORMAT, LOAD, RV32I); }
   class riscv_LHU_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(LHU,    I_FORMAT, LOAD, RV32I); }
   // STORE instructions
   class riscv_SB_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(SB,     S_FORMAT, STORE, RV32I); }
   class riscv_SH_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(SH,     S_FORMAT, STORE, RV32I); }
   class riscv_SW_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(SW,     S_FORMAT, STORE, RV32I); }
   // SHIFT intructions
   class riscv_SLL_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(SLL,    R_FORMAT, SHIFT, RV32I); }
   class riscv_SLLI_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(SLLI,   I_FORMAT, SHIFT, RV32I); }
   class riscv_SRL_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(SRL,    R_FORMAT, SHIFT, RV32I); }
   class riscv_SRLI_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(SRLI,   I_FORMAT, SHIFT, RV32I); }
   class riscv_SRA_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(SRA,    R_FORMAT, SHIFT, RV32I); }
   class riscv_SRAI_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(SRAI,   I_FORMAT, SHIFT, RV32I); }
   // ARITHMETIC intructions
   class riscv_ADD_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(ADD,    R_FORMAT, ARITHMETIC, RV32I); }
   class riscv_ADDI_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(ADDI,   I_FORMAT, ARITHMETIC, RV32I); }
   class riscv_NOP_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(NOP,    I_FORMAT, ARITHMETIC, RV32I); }
   class riscv_SUB_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(SUB,    R_FORMAT, ARITHMETIC, RV32I); }
   class riscv_LUI_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(LUI,    U_FORMAT, ARITHMETIC, RV32I, UIMM); }
   class riscv_AUIPC_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(AUIPC,  U_FORMAT, ARITHMETIC, RV32I, UIMM); }
   // LOGICAL instructions
   class riscv_XOR_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(XOR,    R_FORMAT, LOGICAL, RV32I); }
   class riscv_XORI_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(XORI,   I_FORMAT, LOGICAL, RV32I); }
   class riscv_OR_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(OR,     R_FORMAT, LOGICAL, RV32I); }
   class riscv_ORI_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(ORI,    I_FORMAT, LOGICAL, RV32I); }
   class riscv_AND_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(AND,    R_FORMAT, LOGICAL, RV32I); }
   class riscv_ANDI_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(ANDI,   I_FORMAT, LOGICAL, RV32I); }
   // COMPARE instructions
   class riscv_SLT_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(SLT,    R_FORMAT, COMPARE, RV32I); }
   class riscv_SLTI_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(SLTI,   I_FORMAT, COMPARE, RV32I); }
   class riscv_SLTU_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(SLTU,   R_FORMAT, COMPARE, RV32I); }
   class riscv_SLTIU_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(SLTIU,  I_FORMAT, COMPARE, RV32I); }
   // BRANCH instructions
   class riscv_BEQ_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(BEQ,    B_FORMAT, BRANCH, RV32I); }
   class riscv_BNE_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(BNE,    B_FORMAT, BRANCH, RV32I); }
   class riscv_BLT_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(BLT,    B_FORMAT, BRANCH, RV32I); }
   class riscv_BGE_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(BGE,    B_FORMAT, BRANCH, RV32I); }
   class riscv_BLTU_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(BLTU,   B_FORMAT, BRANCH, RV32I); }
   class riscv_BGEU_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(BGEU,   B_FORMAT, BRANCH, RV32I); }
   // JUMP instructions
   class riscv_JAL_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(JAL,    J_FORMAT, JUMP, RV32I); }
   class riscv_JALR_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(JALR,   I_FORMAT, JUMP, RV32I); }
   // SYNCH instructions
   class riscv_FENCE_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(FENCE,  I_FORMAT, SYNCH, RV32I); }
   class riscv_FENCE_I_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(FENCE_I, I_FORMAT, SYNCH, RV32I); }
   class riscv_SFENCE_VMA_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(SFENCE_VMA, R_FORMAT, SYNCH, RV32I); }
   // SYSTEM instructions
   class riscv_ECALL_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(ECALL,   I_FORMAT, SYSTEM, RV32I); }
   class riscv_EBREAK_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(EBREAK,  I_FORMAT, SYSTEM, RV32I); }
   class riscv_URET_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(URET,    I_FORMAT, SYSTEM, RV32I); }
   class riscv_SRET_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(SRET,    I_FORMAT, SYSTEM, RV32I); }
   class riscv_MRET_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(MRET,    I_FORMAT, SYSTEM, RV32I); }
   class riscv_DRET_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(DRET,    I_FORMAT, SYSTEM, RV32I); }
   class riscv_WFI_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(WFI,     I_FORMAT, INTERRUPT, RV32I); }
   // CSR instructions
   class riscv_CSRRW_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(CSRRW,  R_FORMAT, CSR, RV32I, UIMM); }
   class riscv_CSRRS_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(CSRRS,  R_FORMAT, CSR, RV32I, UIMM); }
   class riscv_CSRRC_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(CSRRC,  R_FORMAT, CSR, RV32I, UIMM); }
   class riscv_CSRRWI_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(CSRRWI, I_FORMAT, CSR, RV32I, UIMM); }
   class riscv_CSRRSI_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(CSRRSI, I_FORMAT, CSR, RV32I, UIMM); }
   class riscv_CSRRCI_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(CSRRCI, I_FORMAT, CSR, RV32I, UIMM); }
 }
