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

module riscv.gen.isa.rv32dc_instr;

import riscv.gen.riscv_defines;

import uvm;

version (RISCV_INSTR_STRING_MIXIN) {
  mixin (riscv_fc_instr_mixin(C_FLD,   CL_FORMAT, LOAD, RV32DC, UIMM));
  mixin (riscv_fc_instr_mixin(C_FSD,   CS_FORMAT, STORE, RV32DC, UIMM));
  mixin (riscv_fc_instr_mixin(C_FLDSP, CI_FORMAT, LOAD, RV32DC, UIMM));
  mixin (riscv_fc_instr_mixin(C_FSDSP, CSS_FORMAT, STORE, RV32DC, UIMM));
 }
 else {
   class riscv_C_FLD_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_FLD,   CL_FORMAT, LOAD, RV32DC, UIMM); }
   class riscv_C_FSD_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_FSD,   CS_FORMAT, STORE, RV32DC, UIMM); }
   class riscv_C_FLDSP_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_FLDSP, CI_FORMAT, LOAD, RV32DC, UIMM); }
   class riscv_C_FSDSP_INSTR: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_FSDSP, CSS_FORMAT, STORE, RV32DC, UIMM); }
 }
