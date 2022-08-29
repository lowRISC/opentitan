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
module riscv.gen.isa.rv32m_instr;

import riscv.gen.riscv_defines;

import uvm;


version (RISCV_INSTR_STRING_MIXIN) {
  ////////////  RV32M instructions  //////////////
  mixin (riscv_instr_mixin(MUL,    R_FORMAT, ARITHMETIC, RV32M));
  mixin (riscv_instr_mixin(MULH,   R_FORMAT, ARITHMETIC, RV32M));
  mixin (riscv_instr_mixin(MULHSU, R_FORMAT, ARITHMETIC, RV32M));
  mixin (riscv_instr_mixin(MULHU,  R_FORMAT, ARITHMETIC, RV32M));
  mixin (riscv_instr_mixin(DIV,    R_FORMAT, ARITHMETIC, RV32M));
  mixin (riscv_instr_mixin(DIVU,   R_FORMAT, ARITHMETIC, RV32M));
  mixin (riscv_instr_mixin(REM,    R_FORMAT, ARITHMETIC, RV32M));
  mixin (riscv_instr_mixin(REMU,   R_FORMAT, ARITHMETIC, RV32M));
 }
 else {
   ////////////  RV32M instructions  //////////////
   class riscv_MUL_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(MUL,    R_FORMAT, ARITHMETIC, RV32M); }
   class riscv_MULH_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(MULH,   R_FORMAT, ARITHMETIC, RV32M); }
   class riscv_MULHSU_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(MULHSU, R_FORMAT, ARITHMETIC, RV32M); }
   class riscv_MULHU_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(MULHU,  R_FORMAT, ARITHMETIC, RV32M); }
   class riscv_DIV_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(DIV,    R_FORMAT, ARITHMETIC, RV32M); }
   class riscv_DIVU_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(DIVU,   R_FORMAT, ARITHMETIC, RV32M); }
   class riscv_REM_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(REM,    R_FORMAT, ARITHMETIC, RV32M); }
   class riscv_REMU_instr: riscv_instr
   { mixin RISCV_INSTR_MIXIN!(REMU,   R_FORMAT, ARITHMETIC, RV32M); }
 }

