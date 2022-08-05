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

module riscv.gen.isa.rv32zbs_instr;

import riscv.gen.riscv_defines;

import uvm;

version (RISCV_INSTR_STRING_MIXIN) {
  mixin (riscv_zbs_instr_mixin(BCLR,  R_FORMAT, SHIFT, RV32ZBS));
  mixin (riscv_zbs_instr_mixin(BCLRI, I_FORMAT, SHIFT, RV32ZBS, UIMM));
  mixin (riscv_zbs_instr_mixin(BEXT,  R_FORMAT, SHIFT, RV32ZBS));
  mixin (riscv_zbs_instr_mixin(BEXTI, I_FORMAT, SHIFT, RV32ZBS, UIMM));
  mixin (riscv_zbs_instr_mixin(BINV,  R_FORMAT, SHIFT, RV32ZBS));
  mixin (riscv_zbs_instr_mixin(BINVI, I_FORMAT, SHIFT, RV32ZBS, UIMM));
  mixin (riscv_zbs_instr_mixin(BSET,  R_FORMAT, SHIFT, RV32ZBS));
  mixin (riscv_zbs_instr_mixin(BSETI, I_FORMAT, SHIFT, RV32ZBS, UIMM));
 }
 else {
   class riscv_BCLR_instr: riscv_zbs_instr
   { mixin RISCV_INSTR_MIXIN!(BCLR,  R_FORMAT, SHIFT, RV32ZBS); }
   class riscv_BCLRI_instr: riscv_zbs_instr
   { mixin RISCV_INSTR_MIXIN!(BCLRI, I_FORMAT, SHIFT, RV32ZBS, UIMM); }
   class riscv_BEXT_instr: riscv_zbs_instr
   { mixin RISCV_INSTR_MIXIN!(BEXT,  R_FORMAT, SHIFT, RV32ZBS); }
   class riscv_BEXTI_instr: riscv_zbs_instr
   { mixin RISCV_INSTR_MIXIN!(BEXTI, I_FORMAT, SHIFT, RV32ZBS, UIMM); }
   class riscv_BINV_instr: riscv_zbs_instr
   { mixin RISCV_INSTR_MIXIN!(BINV,  R_FORMAT, SHIFT, RV32ZBS); }
   class riscv_BINVI_instr: riscv_zbs_instr
   { mixin RISCV_INSTR_MIXIN!(BINVI, I_FORMAT, SHIFT, RV32ZBS, UIMM); }
   class riscv_BSET_instr: riscv_zbs_instr
   { mixin RISCV_INSTR_MIXIN!(BSET,  R_FORMAT, SHIFT, RV32ZBS); }
   class riscv_BSETI_instr: riscv_zbs_instr
   { mixin RISCV_INSTR_MIXIN!(BSETI, I_FORMAT, SHIFT, RV32ZBS, UIMM); }
 }
