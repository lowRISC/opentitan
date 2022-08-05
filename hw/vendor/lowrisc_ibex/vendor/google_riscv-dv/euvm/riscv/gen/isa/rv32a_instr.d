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

module riscv.gen.isa.rv32a_instr;

import riscv.gen.riscv_defines;

import uvm;

version (RISCV_INSTR_STRING_MIXIN) {
  mixin (riscv_amo_instr_mixin(LR_W,      R_FORMAT, LOAD,  RV32A));
  mixin (riscv_amo_instr_mixin(SC_W,      R_FORMAT, STORE, RV32A));
  mixin (riscv_amo_instr_mixin(AMOSWAP_W, R_FORMAT, AMO,   RV32A));
  mixin (riscv_amo_instr_mixin(AMOADD_W,  R_FORMAT, AMO,   RV32A));
  mixin (riscv_amo_instr_mixin(AMOAND_W,  R_FORMAT, AMO,   RV32A));
  mixin (riscv_amo_instr_mixin(AMOOR_W,   R_FORMAT, AMO,   RV32A));
  mixin (riscv_amo_instr_mixin(AMOXOR_W,  R_FORMAT, AMO,   RV32A));
  mixin (riscv_amo_instr_mixin(AMOMIN_W,  R_FORMAT, AMO,   RV32A));
  mixin (riscv_amo_instr_mixin(AMOMAX_W,  R_FORMAT, AMO,   RV32A));
  mixin (riscv_amo_instr_mixin(AMOMINU_W, R_FORMAT, AMO,   RV32A));
  mixin (riscv_amo_instr_mixin(AMOMAXU_W, R_FORMAT, AMO,   RV32A));
 }
 else {
   class riscv_LR_W_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(LR_W,      R_FORMAT, LOAD,  RV32A); }
   class riscv_SC_W_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(SC_W,      R_FORMAT, STORE, RV32A); }
   class riscv_AMOSWAP_W_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOSWAP_W, R_FORMAT, AMO,   RV32A); }
   class riscv_AMOADD_W_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOADD_W,  R_FORMAT, AMO,   RV32A); }
   class riscv_AMOAND_W_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOAND_W,  R_FORMAT, AMO,   RV32A); }
   class riscv_AMOOR_W_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOOR_W,   R_FORMAT, AMO,   RV32A); }
   class riscv_AMOXOR_W_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOXOR_W,  R_FORMAT, AMO,   RV32A); }
   class riscv_AMOMIN_W_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOMIN_W,  R_FORMAT, AMO,   RV32A); }
   class riscv_AMOMAX_W_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOMAX_W,  R_FORMAT, AMO,   RV32A); }
   class riscv_AMOMINU_W_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOMINU_W, R_FORMAT, AMO,   RV32A); }
   class riscv_AMOMAXU_W_instr: riscv_amo_instr
   { mixin RISCV_INSTR_MIXIN!(AMOMAXU_W, R_FORMAT, AMO,   RV32A); }
 }
