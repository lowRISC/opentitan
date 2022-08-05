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

module riscv.gen.isa.rv128c_instr;

import riscv.gen.riscv_defines;

import uvm;

version (RISCV_INSTR_STRING_MIXIN) {
  mixin (riscv_c_instr_mixin(C_SRLI64, CB_FORMAT, SHIFT, RV128C, NZUIMM));
  mixin (riscv_c_instr_mixin(C_SRAI64, CB_FORMAT, SHIFT, RV128C, NZUIMM));
  mixin (riscv_c_instr_mixin(C_SLLI64, CI_FORMAT, SHIFT, RV128C, NZUIMM));
  mixin (riscv_c_instr_mixin(C_LQ,     CL_FORMAT, LOAD, RV32DC, UIMM));
  mixin (riscv_c_instr_mixin(C_SQ,     CS_FORMAT, STORE, RV32DC, UIMM));
  mixin (riscv_c_instr_mixin(C_LQSP,   CI_FORMAT, LOAD, RV32DC, UIMM));
  mixin (riscv_c_instr_mixin(C_SQSP,   CSS_FORMAT, STORE, RV32DC, UIMM));
 }
 else {
   class riscv_C_SRLI64_instr: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_SRLI64, CB_FORMAT, SHIFT, RV128C, NZUIMM); }
   class riscv_C_SRAI64_instr: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_SRAI64, CB_FORMAT, SHIFT, RV128C, NZUIMM); }
   class riscv_C_SLLI64_instr: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_SLLI64, CI_FORMAT, SHIFT, RV128C, NZUIMM); }
   class riscv_C_LQ_instr: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_LQ,     CL_FORMAT, LOAD, RV32DC, UIMM); }
   class riscv_C_SQ_instr: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_SQ,     CS_FORMAT, STORE, RV32DC, UIMM); }
   class riscv_C_LQSP_instr: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_LQSP,   CI_FORMAT, LOAD, RV32DC, UIMM); }
   class riscv_C_SQSP_instr: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_SQSP,   CSS_FORMAT, STORE, RV32DC, UIMM); }
 }
