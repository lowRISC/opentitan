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

module riscv.gen.isa.rv32f_instr;

import riscv.gen.riscv_defines;

import uvm;

version (RISCV_INSTR_STRING_MIXIN) {
  mixin (riscv_fp_instr_mixin(FLW,       I_FORMAT, LOAD, RV32F));
  mixin (riscv_fp_instr_mixin(FSW,       S_FORMAT, STORE, RV32F));
  mixin (riscv_fp_instr_mixin(FMADD_S,   R4_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FMSUB_S,   R4_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FNMSUB_S,  R4_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FNMADD_S,  R4_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FADD_S,    R_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FSUB_S,    R_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FMUL_S,    R_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FDIV_S,    R_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FSQRT_S,   I_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FSGNJ_S,   R_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FSGNJN_S,  R_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FSGNJX_S,  R_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FMIN_S,    R_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FMAX_S,    R_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FCVT_W_S,  I_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FCVT_WU_S, I_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FMV_X_W,   I_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FEQ_S,     R_FORMAT, COMPARE, RV32F));
  mixin (riscv_fp_instr_mixin(FLT_S,     R_FORMAT, COMPARE, RV32F));
  mixin (riscv_fp_instr_mixin(FLE_S,     R_FORMAT, COMPARE, RV32F));
  mixin (riscv_fp_instr_mixin(FCLASS_S,  R_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FCVT_S_W,  I_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FCVT_S_WU, I_FORMAT, ARITHMETIC, RV32F));
  mixin (riscv_fp_instr_mixin(FMV_W_X,   I_FORMAT, ARITHMETIC, RV32F));
 }
 else {
   class riscv_FLW_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FLW,       I_FORMAT, LOAD, RV32F); }
   class riscv_FSW_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FSW,       S_FORMAT, STORE, RV32F); }
   class riscv_FMADD_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FMADD_S,   R4_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FMSUB_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FMSUB_S,   R4_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FNMSUB_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FNMSUB_S,  R4_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FNMADD_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FNMADD_S,  R4_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FADD_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FADD_S,    R_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FSUB_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FSUB_S,    R_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FMUL_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FMUL_S,    R_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FDIV_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FDIV_S,    R_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FSQRT_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FSQRT_S,   I_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FSGNJ_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FSGNJ_S,   R_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FSGNJN_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FSGNJN_S,  R_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FSGNJX_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FSGNJX_S,  R_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FMIN_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FMIN_S,    R_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FMAX_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FMAX_S,    R_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FCVT_W_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_W_S,  I_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FCVT_WU_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_WU_S, I_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FMV_X_W_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FMV_X_W,   I_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FEQ_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FEQ_S,     R_FORMAT, COMPARE, RV32F); }
   class riscv_FLT_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FLT_S,     R_FORMAT, COMPARE, RV32F); }
   class riscv_FLE_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FLE_S,     R_FORMAT, COMPARE, RV32F); }
   class riscv_FCLASS_S_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCLASS_S,  R_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FCVT_S_W_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_S_W,  I_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FCVT_S_WU_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_S_WU, I_FORMAT, ARITHMETIC, RV32F); }
   class riscv_FMV_W_X_instr: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FMV_W_X,   I_FORMAT, ARITHMETIC, RV32F); }
 }
