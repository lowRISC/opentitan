/*
 * Copyright 2020 Google LLC
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

module riscv.gen.isa.rv64a_instr;

import riscv.gen.riscv_defines;

import uvm;

version (RISCV_INSTR_STRING_MIXIN) {
  mixin (riscv_amo_instr_mixin(LR_D,      R_FORMAT, LOAD, RV64A));
  mixin (riscv_amo_instr_mixin(SC_D,      R_FORMAT, STORE, RV64A));
  mixin (riscv_amo_instr_mixin(AMOSWAP_D, R_FORMAT, AMO, RV64A));
  mixin (riscv_amo_instr_mixin(AMOADD_D,  R_FORMAT, AMO, RV64A));
  mixin (riscv_amo_instr_mixin(AMOAND_D,  R_FORMAT, AMO, RV64A));
  mixin (riscv_amo_instr_mixin(AMOOR_D,   R_FORMAT, AMO, RV64A));
  mixin (riscv_amo_instr_mixin(AMOXOR_D,  R_FORMAT, AMO, RV64A));
  mixin (riscv_amo_instr_mixin(AMOMIN_D,  R_FORMAT, AMO, RV64A));
  mixin (riscv_amo_instr_mixin(AMOMAX_D,  R_FORMAT, AMO, RV64A));
  mixin (riscv_amo_instr_mixin(AMOMINU_D, R_FORMAT, AMO, RV64A));
  mixin (riscv_amo_instr_mixin(AMOMAXU_D, R_FORMAT, AMO, RV64A));
 }
 else {
   class riscv_LR_D_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(LR_D,      R_FORMAT, LOAD, RV64A); }
   class riscv_SC_D_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(SC_D,      R_FORMAT, STORE, RV64A); }
   class riscv_AMOSWAP_D_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOSWAP_D, R_FORMAT, AMO, RV64A); }
   class riscv_AMOADD_D_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOADD_D,  R_FORMAT, AMO, RV64A); }
   class riscv_AMOAND_D_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOAND_D,  R_FORMAT, AMO, RV64A); }
   class riscv_AMOOR_D_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOOR_D,   R_FORMAT, AMO, RV64A); }
   class riscv_AMOXOR_D_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOXOR_D,  R_FORMAT, AMO, RV64A); }
   class riscv_AMOMIN_D_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOMIN_D,  R_FORMAT, AMO, RV64A); }
   class riscv_AMOMAX_D_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOMAX_D,  R_FORMAT, AMO, RV64A); }
   class riscv_AMOMINU_D_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOMINU_D, R_FORMAT, AMO, RV64A); }
   class riscv_AMOMAXU_D_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOMAXU_D, R_FORMAT, AMO, RV64A); }
 }
