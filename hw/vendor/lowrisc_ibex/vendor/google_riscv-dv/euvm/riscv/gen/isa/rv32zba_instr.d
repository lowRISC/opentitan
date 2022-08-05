/*
 * Copyright 2018 Google LLC
 * Copyright 2021 Silicon Labs, Inc.
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

module riscv.gen.isa.rv32zba_instr;

import riscv.gen.riscv_defines;

import uvm;

version (RISCV_INSTR_STRING_MIXIN) {
  mixin (riscv_zba_instr_mixin(SH1ADD, R_FORMAT, ARITHMETIC, RV32ZBA));
  mixin (riscv_zba_instr_mixin(SH2ADD, R_FORMAT, ARITHMETIC, RV32ZBA));
  mixin (riscv_zba_instr_mixin(SH3ADD, R_FORMAT, ARITHMETIC, RV32ZBA));
 }
 else {
   class riscv_SH1ADD_instr: riscv_zba_instr
   { mixin RISCV_INSTR_MIXIN!(SH1ADD, R_FORMAT, ARITHMETIC, RV32ZBA); }
   class riscv_SH2ADD_instr: riscv_zba_instr
   { mixin RISCV_INSTR_MIXIN!(SH2ADD, R_FORMAT, ARITHMETIC, RV32ZBA); }
   class riscv_SH3ADD_instr: riscv_zba_instr
   { mixin RISCV_INSTR_MIXIN!(SH3ADD, R_FORMAT, ARITHMETIC, RV32ZBA); }
 }
