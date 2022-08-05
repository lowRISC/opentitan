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

module riscv.gen.isa.rv64f_instr;

import riscv.gen.riscv_defines;

import uvm;

version (RISCV_INSTR_STRING_MIXIN) {
  mixin (riscv_fp_instr_mixin(FCVT_L_S,  I_FORMAT, ARITHMETIC, RV64F));
  mixin (riscv_fp_instr_mixin(FCVT_LU_S, I_FORMAT, ARITHMETIC, RV64F));
  mixin (riscv_fp_instr_mixin(FCVT_S_L,  I_FORMAT, ARITHMETIC, RV64F));
  mixin (riscv_fp_instr_mixin(FCVT_S_LU, I_FORMAT, ARITHMETIC, RV64F));
 }
 else {
   class riscv_FCVT_L_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_L_S,  I_FORMAT, ARITHMETIC, RV64F); }
   class riscv_FCVT_LU_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_LU_S, I_FORMAT, ARITHMETIC, RV64F); }
   class riscv_FCVT_S_L_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_S_L,  I_FORMAT, ARITHMETIC, RV64F); }
   class riscv_FCVT_S_LU_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_S_LU, I_FORMAT, ARITHMETIC, RV64F); }
 }
