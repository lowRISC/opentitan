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

module riscv.gen.isa.rv32zbc_instr;

import riscv.gen.riscv_defines;

import uvm;

version (RISCV_INSTR_STRING_MIXIN) {
  mixin (riscv_zbc_instr_mixin(CLMUL,  R_FORMAT, ARITHMETIC, RV32ZBC));
  mixin (riscv_zbc_instr_mixin(CLMULH, R_FORMAT, ARITHMETIC, RV32ZBC));
  mixin (riscv_zbc_instr_mixin(CLMULR, R_FORMAT, ARITHMETIC, RV32ZBC));
 }
 else {
   class riscv_CLMUL_instr: riscv_zbc_instr
   { mixin RISCV_INSTR_MIXIN!(CLMUL,  R_FORMAT, ARITHMETIC, RV32ZBC); }
   class riscv_CLMULH_instr: riscv_zbc_instr
   { mixin RISCV_INSTR_MIXIN!(CLMULH, R_FORMAT, ARITHMETIC, RV32ZBC); }
   class riscv_CLMULR_instr: riscv_zbc_instr
   { mixin RISCV_INSTR_MIXIN!(CLMULR, R_FORMAT, ARITHMETIC, RV32ZBC); }
 }
