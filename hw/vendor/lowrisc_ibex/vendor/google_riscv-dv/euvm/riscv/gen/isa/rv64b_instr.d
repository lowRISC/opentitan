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

module riscv.gen.isa.rv64b_instr;

import riscv.gen.riscv_defines;

import uvm;

// Remaining bitmanip instructions of draft v.0.93 not ratified in v.1.00 (Zba, Zbb, Zbc, Zbs).

version (RISCV_INSTR_STRING_MIXIN) {
  // ARITHMETIC intructions
  mixin (riscv_b_instr_mixin(BMATOR,       R_FORMAT, ARITHMETIC, RV64B));
  mixin (riscv_b_instr_mixin(BMATXOR,      R_FORMAT, ARITHMETIC, RV64B));
  mixin (riscv_b_instr_mixin(BMATFLIP,     R_FORMAT, ARITHMETIC, RV64B));
  mixin (riscv_b_instr_mixin(CRC32_D,      R_FORMAT, ARITHMETIC, RV64B));
  mixin (riscv_b_instr_mixin(CRC32C_D,     R_FORMAT, ARITHMETIC, RV64B));
  mixin (riscv_b_instr_mixin(SHFLW,        R_FORMAT, ARITHMETIC, RV64B));
  mixin (riscv_b_instr_mixin(UNSHFLW,      R_FORMAT, ARITHMETIC, RV64B));
  mixin (riscv_b_instr_mixin(BCOMPRESSW,   R_FORMAT, ARITHMETIC, RV64B));
  mixin (riscv_b_instr_mixin(BDECOMPRESSW, R_FORMAT, ARITHMETIC, RV64B));
  mixin (riscv_b_instr_mixin(BFPW,         R_FORMAT, ARITHMETIC, RV64B));
  // SHIFT intructions
  mixin (riscv_b_instr_mixin(SLOW,    R_FORMAT, SHIFT, RV64B));
  mixin (riscv_b_instr_mixin(SROW,    R_FORMAT, SHIFT, RV64B));
  mixin (riscv_b_instr_mixin(SLOIW,   I_FORMAT, SHIFT, RV64B, UIMM));
  mixin (riscv_b_instr_mixin(SROIW,   I_FORMAT, SHIFT, RV64B, UIMM));
  mixin (riscv_b_instr_mixin(GREVW,   R_FORMAT, SHIFT, RV64B));
  mixin (riscv_b_instr_mixin(GREVIW,  I_FORMAT, SHIFT, RV64B, UIMM));
  mixin (riscv_b_instr_mixin(FSLW,   R4_FORMAT, SHIFT, RV64B));
  mixin (riscv_b_instr_mixin(FSRW,   R4_FORMAT, SHIFT, RV64B));
  mixin (riscv_b_instr_mixin(FSRIW,   I_FORMAT, SHIFT, RV64B, UIMM));
  // LOGICAL instructions
  mixin (riscv_b_instr_mixin(GORCW,   R_FORMAT, LOGICAL, RV64B));
  mixin (riscv_b_instr_mixin(GORCIW,  I_FORMAT, LOGICAL, RV64B, UIMM));
  mixin (riscv_b_instr_mixin(PACKW,   R_FORMAT, LOGICAL, RV64B));
  mixin (riscv_b_instr_mixin(PACKUW,  R_FORMAT, LOGICAL, RV64B));
  mixin (riscv_b_instr_mixin(XPERM_W, R_FORMAT, LOGICAL, RV64B));
 }
 else {
  // ARITHMETIC intructions
   class riscv_BMATOR_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(BMATOR,       R_FORMAT, ARITHMETIC, RV64B); }
   class riscv_BMATXOR_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(BMATXOR,      R_FORMAT, ARITHMETIC, RV64B); }
   class riscv_BMATFLIP_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(BMATFLIP,     R_FORMAT, ARITHMETIC, RV64B); }
   class riscv_CRC32_D_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(CRC32_D,      R_FORMAT, ARITHMETIC, RV64B); }
   class riscv_CRC32C_D_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(CRC32C_D,     R_FORMAT, ARITHMETIC, RV64B); }
   class riscv_SHFLW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(SHFLW,        R_FORMAT, ARITHMETIC, RV64B); }
   class riscv_UNSHFLW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(UNSHFLW,      R_FORMAT, ARITHMETIC, RV64B); }
   class riscv_BCOMPRESSW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(BCOMPRESSW,   R_FORMAT, ARITHMETIC, RV64B); }
   class riscv_BDECOMPRESSW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(BDECOMPRESSW, R_FORMAT, ARITHMETIC, RV64B); }
   class riscv_BFPW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(BFPW,         R_FORMAT, ARITHMETIC, RV64B); }
  // SHIFT intructions
   class riscv_SLOW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(SLOW,    R_FORMAT, SHIFT, RV64B); }
   class riscv_SROW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(SROW,    R_FORMAT, SHIFT, RV64B); }
   class riscv_SLOIW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(SLOIW,   I_FORMAT, SHIFT, RV64B, UIMM); }
   class riscv_SROIW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(SROIW,   I_FORMAT, SHIFT, RV64B, UIMM); }
   class riscv_GREVW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(GREVW,   R_FORMAT, SHIFT, RV64B); }
   class riscv_GREVIW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(GREVIW,  I_FORMAT, SHIFT, RV64B, UIMM); }
   class riscv_FSLW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(FSLW,   R4_FORMAT, SHIFT, RV64B); }
   class riscv_FSRW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(FSRW,   R4_FORMAT, SHIFT, RV64B); }
   class riscv_FSRIW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(FSRIW,   I_FORMAT, SHIFT, RV64B, UIMM); }
  // LOGICAL instructions
   class riscv_GORCW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(GORCW,   R_FORMAT, LOGICAL, RV64B); }
   class riscv_GORCIW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(GORCIW,  I_FORMAT, LOGICAL, RV64B, UIMM); }
   class riscv_PACKW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(PACKW,   R_FORMAT, LOGICAL, RV64B); }
   class riscv_PACKUW_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(PACKUW,  R_FORMAT, LOGICAL, RV64B); }
   class riscv_XPERM_W_instr: riscv_b_instr
   { mixin RISCV_INSTR_MIXIN!(XPERM_W, R_FORMAT, LOGICAL, RV64B); }
 }
