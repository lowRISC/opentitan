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

module riscv.gen.isa.rv32d_instr;

import riscv.gen.riscv_defines;

import uvm;

version (RISCV_INSTR_STRING_MIXIN) {
  mixin (riscv_fp_instr_mixin(FLD,       I_FORMAT, LOAD, RV32D));
  mixin (riscv_fp_instr_mixin(FSD,       S_FORMAT, STORE, RV32D));
  mixin (riscv_fp_instr_mixin(FMADD_D,   R4_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FMSUB_D,   R4_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FNMSUB_D,  R4_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FNMADD_D,  R4_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FADD_D,    R_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FSUB_D,    R_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FMUL_D,    R_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FDIV_D,    R_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FSQRT_D,   I_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FSGNJ_D,   R_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FSGNJN_D,  R_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FSGNJX_D,  R_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FMIN_D,    R_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FMAX_D,    R_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FCVT_S_D,  I_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FCVT_D_S,  I_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FEQ_D,     R_FORMAT, COMPARE, RV32D));
  mixin (riscv_fp_instr_mixin(FLT_D,     R_FORMAT, COMPARE, RV32D));
  mixin (riscv_fp_instr_mixin(FLE_D,     R_FORMAT, COMPARE, RV32D));
  mixin (riscv_fp_instr_mixin(FCLASS_D,  R_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FCVT_W_D,  I_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FCVT_WU_D, I_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FCVT_D_W,  I_FORMAT, ARITHMETIC, RV32D));
  mixin (riscv_fp_instr_mixin(FCVT_D_WU, I_FORMAT, ARITHMETIC, RV32D));
 }
 else {
   class riscv_FLD_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FLD,       I_FORMAT, LOAD, RV32D); }
   class riscv_FSD_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FSD,       S_FORMAT, STORE, RV32D); }
   class riscv_FMADD_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FMADD_D,   R4_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FMSUB_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FMSUB_D,   R4_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FNMSUB_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FNMSUB_D,  R4_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FNMADD_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FNMADD_D,  R4_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FADD_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FADD_D,    R_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FSUB_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FSUB_D,    R_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FMUL_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FMUL_D,    R_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FDIV_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FDIV_D,    R_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FSQRT_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FSQRT_D,   I_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FSGNJ_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FSGNJ_D,   R_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FSGNJN_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FSGNJN_D,  R_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FSGNJX_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FSGNJX_D,  R_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FMIN_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FMIN_D,    R_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FMAX_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FMAX_D,    R_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FCVT_S_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_S_D,  I_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FCVT_D_S_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_D_S,  I_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FEQ_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FEQ_D,     R_FORMAT, COMPARE, RV32D); }
   class riscv_FLT_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FLT_D,     R_FORMAT, COMPARE, RV32D); }
   class riscv_FLE_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FLE_D,     R_FORMAT, COMPARE, RV32D); }
   class riscv_FCLASS_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCLASS_D,  R_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FCVT_W_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_W_D,  I_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FCVT_WU_D_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_WU_D, I_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FCVT_D_W_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_D_W,  I_FORMAT, ARITHMETIC, RV32D); }
   class riscv_FCVT_D_WU_INSTR: riscv_floating_point_instr
   { mixin RISCV_INSTR_MIXIN!(FCVT_D_WU, I_FORMAT, ARITHMETIC, RV32D); }
 }
