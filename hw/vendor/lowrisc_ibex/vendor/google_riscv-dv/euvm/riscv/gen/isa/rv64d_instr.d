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

module riscv.gen.isa.rv64d_instr;

import riscv.gen.riscv_defines;

import uvm;

version (RISCV_INSTR_STRING_MIXIN) {
  mixin (riscv_fp_instr_mixin(FMV_X_D,   I_FORMAT, ARITHMETIC, RV64D));
  mixin (riscv_fp_instr_mixin(FMV_D_X,   I_FORMAT, ARITHMETIC, RV64D));
  mixin (riscv_fp_instr_mixin(FCVT_L_D,  I_FORMAT, ARITHMETIC, RV64D));
  mixin (riscv_fp_instr_mixin(FCVT_LU_D, I_FORMAT, ARITHMETIC, RV64D));
  mixin (riscv_fp_instr_mixin(FCVT_D_L,  I_FORMAT, ARITHMETIC, RV64D));
  mixin (riscv_fp_instr_mixin(FCVT_D_LU, I_FORMAT, ARITHMETIC, RV64D));
 }
 else {
   class riscv_FMV_X_D_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FMV_X_D,   I_FORMAT, ARITHMETIC, RV64D); }
   class riscv_FMV_D_X_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FMV_D_X,   I_FORMAT, ARITHMETIC, RV64D); }
   class riscv_FCVT_L_D_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_L_D,  I_FORMAT, ARITHMETIC, RV64D); }
   class riscv_FCVT_LU_D_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_LU_D, I_FORMAT, ARITHMETIC, RV64D); }
   class riscv_FCVT_D_L_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_D_L,  I_FORMAT, ARITHMETIC, RV64D); }
   class riscv_FCVT_D_LU_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_D_LU, I_FORMAT, ARITHMETIC, RV64D); }
 }
