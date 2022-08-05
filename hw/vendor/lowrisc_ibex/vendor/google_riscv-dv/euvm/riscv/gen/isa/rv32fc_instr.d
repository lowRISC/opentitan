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

module riscv.gen.isa.rv32fc_instr;

import riscv.gen.riscv_defines;

import uvm;


version (RISCV_INSTR_STRING_MIXIN) {
  mixin (riscv_fc_instr_mixin(C_FLW,   CL_FORMAT, LOAD, RV32FC, UIMM));
  mixin (riscv_fc_instr_mixin(C_FSW,   CS_FORMAT, STORE, RV32FC, UIMM));
  mixin (riscv_fc_instr_mixin(C_FLWSP, CI_FORMAT, LOAD, RV32FC, UIMM));
  mixin (riscv_fc_instr_mixin(C_FSWSP, CSS_FORMAT, STORE, RV32FC, UIMM));
 }
 else {
   class riscv_C_FLW_instr: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_FLW,   CL_FORMAT, LOAD, RV32FC, UIMM); }
   class riscv_C_FSW_instr: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_FSW,   CS_FORMAT, STORE, RV32FC, UIMM); }
   class riscv_C_FLWSP_instr: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_FLWSP, CI_FORMAT, LOAD, RV32FC, UIMM); }
   class riscv_C_FSWSP_instr: riscv_compressed_instr
   { mixin RISCV_INSTR_MIXIN!(C_FSWSP, CSS_FORMAT, STORE, RV32FC, UIMM); }
 }
