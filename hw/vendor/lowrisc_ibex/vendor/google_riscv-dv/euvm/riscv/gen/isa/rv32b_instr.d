/*
 * Copyright 2019 Google LLC
 * Copyright 2019 Mellanox Technologies Ltd
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

module riscv.gen.isa.rv32b_instr;

import riscv.gen.riscv_defines;

import uvm;

// Remaining bitmanip instructions of draft v.0.93 not ratified in v.1.00 (Zba, Zbb, Zbc, Zbs).

version (RISCV_INSTR_STRING_MIXIN) {
  // LOGICAL instructions
  mixin (riscv_b_instr_mixin(GORC,     R_FORMAT, LOGICAL, RV32B));
  mixin (riscv_b_instr_mixin(GORCI,    I_FORMAT, LOGICAL, RV32B, UIMM));
  mixin (riscv_b_instr_mixin(CMIX,    R4_FORMAT, LOGICAL, RV32B));
  mixin (riscv_b_instr_mixin(CMOV,    R4_FORMAT, LOGICAL, RV32B));
  mixin (riscv_b_instr_mixin(PACK,     R_FORMAT, LOGICAL, RV32B));
  mixin (riscv_b_instr_mixin(PACKU,    R_FORMAT, LOGICAL, RV32B));
  mixin (riscv_b_instr_mixin(PACKH,    R_FORMAT, LOGICAL, RV32B));
  mixin (riscv_b_instr_mixin(XPERM_N,  R_FORMAT, LOGICAL, RV32B));
  mixin (riscv_b_instr_mixin(XPERM_B,  R_FORMAT, LOGICAL, RV32B));
  mixin (riscv_b_instr_mixin(XPERM_H,  R_FORMAT, LOGICAL, RV32B));
  // SHIFT intructions
  mixin (riscv_b_instr_mixin(SLO,    R_FORMAT, SHIFT, RV32B));
  mixin (riscv_b_instr_mixin(SRO,    R_FORMAT, SHIFT, RV32B));
  mixin (riscv_b_instr_mixin(SLOI,   I_FORMAT, SHIFT, RV32B, UIMM));
  mixin (riscv_b_instr_mixin(SROI,   I_FORMAT, SHIFT, RV32B, UIMM));
  mixin (riscv_b_instr_mixin(GREV,   R_FORMAT, SHIFT, RV32B));
  mixin (riscv_b_instr_mixin(GREVI,  I_FORMAT, SHIFT, RV32B, UIMM));
  mixin (riscv_b_instr_mixin(FSL,   R4_FORMAT, SHIFT, RV32B));
  mixin (riscv_b_instr_mixin(FSR,   R4_FORMAT, SHIFT, RV32B));
  mixin (riscv_b_instr_mixin(FSRI,   I_FORMAT, SHIFT, RV32B, UIMM));
  // ARITHMETIC intructions
  mixin (riscv_b_instr_mixin(CRC32_B,     R_FORMAT, ARITHMETIC, RV32B));
  mixin (riscv_b_instr_mixin(CRC32_H,     R_FORMAT, ARITHMETIC, RV32B));
  mixin (riscv_b_instr_mixin(CRC32_W,     R_FORMAT, ARITHMETIC, RV32B));
  mixin (riscv_b_instr_mixin(CRC32C_B,    R_FORMAT, ARITHMETIC, RV32B));
  mixin (riscv_b_instr_mixin(CRC32C_H,    R_FORMAT, ARITHMETIC, RV32B));
  mixin (riscv_b_instr_mixin(CRC32C_W,    R_FORMAT, ARITHMETIC, RV32B));
  mixin (riscv_b_instr_mixin(SHFL,        R_FORMAT, ARITHMETIC, RV32B));
  mixin (riscv_b_instr_mixin(UNSHFL,      R_FORMAT, ARITHMETIC, RV32B));
  mixin (riscv_b_instr_mixin(SHFLI,       I_FORMAT, ARITHMETIC, RV32B, UIMM));
  mixin (riscv_b_instr_mixin(UNSHFLI,     I_FORMAT, ARITHMETIC, RV32B, UIMM));
  mixin (riscv_b_instr_mixin(BCOMPRESS,   R_FORMAT, ARITHMETIC, RV32B));
  mixin (riscv_b_instr_mixin(BDECOMPRESS, R_FORMAT, ARITHMETIC, RV32B));
  mixin (riscv_b_instr_mixin(BFP,         R_FORMAT, ARITHMETIC, RV32B));
}
 else {
   // LOGICAL instructions
   class riscv_GORC_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(GORC,     R_FORMAT, LOGICAL, RV32B); }
   class riscv_GORCI_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(GORCI,    I_FORMAT, LOGICAL, RV32B, UIMM); }
   class riscv_CMIX_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(CMIX,    R4_FORMAT, LOGICAL, RV32B); }
   class riscv_CMOV_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(CMOV,    R4_FORMAT, LOGICAL, RV32B); }
   class riscv_PACK_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(PACK,     R_FORMAT, LOGICAL, RV32B); }
   class riscv_PACKU_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(PACKU,    R_FORMAT, LOGICAL, RV32B); }
   class riscv_PACKH_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(PACKH,    R_FORMAT, LOGICAL, RV32B); }
   class riscv_XPERM_N_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(XPERM_N,  R_FORMAT, LOGICAL, RV32B); }
   class riscv_XPERM_B_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(XPERM_B,  R_FORMAT, LOGICAL, RV32B); }
   class riscv_XPERM_H_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(XPERM_H,  R_FORMAT, LOGICAL, RV32B); }
   // SHIFT intructions
   class riscv_SLO_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(SLO,    R_FORMAT, SHIFT, RV32B); }
   class riscv_SRO_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(SRO,    R_FORMAT, SHIFT, RV32B); }
   class riscv_SLOI_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(SLOI,   I_FORMAT, SHIFT, RV32B, UIMM); }
   class riscv_SROI_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(SROI,   I_FORMAT, SHIFT, RV32B, UIMM); }
   class riscv_GREV_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(GREV,   R_FORMAT, SHIFT, RV32B); }
   class riscv_GREVI_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(GREVI,  I_FORMAT, SHIFT, RV32B, UIMM); }
   class riscv_FSL_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(FSL,   R4_FORMAT, SHIFT, RV32B); }
   class riscv_FSR_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(FSR,   R4_FORMAT, SHIFT, RV32B); }
   class riscv_FSRI_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(FSRI,   I_FORMAT, SHIFT, RV32B, UIMM); }
   // ARITHMETIC intructions
   class riscv_CRC32_B_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(CRC32_B,     R_FORMAT, ARITHMETIC, RV32B); }
   class riscv_CRC32_H_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(CRC32_H,     R_FORMAT, ARITHMETIC, RV32B); }
   class riscv_CRC32_W_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(CRC32_W,     R_FORMAT, ARITHMETIC, RV32B); }
   class riscv_CRC32C_B_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(CRC32C_B,    R_FORMAT, ARITHMETIC, RV32B); }
   class riscv_CRC32C_H_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(CRC32C_H,    R_FORMAT, ARITHMETIC, RV32B); }
   class riscv_CRC32C_W_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(CRC32C_W,    R_FORMAT, ARITHMETIC, RV32B); }
   class riscv_SHFL_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(SHFL,        R_FORMAT, ARITHMETIC, RV32B); }
   class riscv_UNSHFL_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(UNSHFL,      R_FORMAT, ARITHMETIC, RV32B); }
   class riscv_SHFLI_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(SHFLI,       I_FORMAT, ARITHMETIC, RV32B, UIMM); }
   class riscv_UNSHFLI_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(UNSHFLI,     I_FORMAT, ARITHMETIC, RV32B, UIMM); }
   class riscv_BCOMPRESS_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(BCOMPRESS,   R_FORMAT, ARITHMETIC, RV32B); }
   class riscv_BDECOMPRESS_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(BDECOMPRESS, R_FORMAT, ARITHMETIC, RV32B); }
   class riscv_BFP_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(BFP,         R_FORMAT, ARITHMETIC, RV32B); }
 }
