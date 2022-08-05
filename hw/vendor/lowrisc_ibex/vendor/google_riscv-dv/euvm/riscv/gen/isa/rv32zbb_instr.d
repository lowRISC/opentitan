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

module riscv.gen.isa.rv32zbb_instr;

import riscv.gen.riscv_defines;

import uvm;

version (RISCV_INSTR_STRING_MIXIN) {
  mixin (riscv_zbb_instr_mixin(ANDN,   R_FORMAT, LOGICAL,    RV32ZBB));
  mixin (riscv_zbb_instr_mixin(CLZ,    I_FORMAT, ARITHMETIC, RV32ZBB));
  mixin (riscv_zbb_instr_mixin(CPOP,   I_FORMAT, ARITHMETIC, RV32ZBB));
  mixin (riscv_zbb_instr_mixin(CTZ,    I_FORMAT, ARITHMETIC, RV32ZBB));
  mixin (riscv_zbb_instr_mixin(MAX,    R_FORMAT, ARITHMETIC, RV32ZBB));
  mixin (riscv_zbb_instr_mixin(MAXU,   R_FORMAT, ARITHMETIC, RV32ZBB));
  mixin (riscv_zbb_instr_mixin(MIN,    R_FORMAT, ARITHMETIC, RV32ZBB));
  mixin (riscv_zbb_instr_mixin(MINU,   R_FORMAT, ARITHMETIC, RV32ZBB));
  mixin (riscv_zbb_instr_mixin(ORC_B,  I_FORMAT, LOGICAL,    RV32ZBB));
  mixin (riscv_zbb_instr_mixin(ORN,    R_FORMAT, LOGICAL,    RV32ZBB));
  mixin (riscv_zbb_instr_mixin(REV8,   I_FORMAT, SHIFT,      RV32ZBB));
  mixin (riscv_zbb_instr_mixin(ROL,    R_FORMAT, SHIFT,      RV32ZBB));
  mixin (riscv_zbb_instr_mixin(ROR,    R_FORMAT, SHIFT,      RV32ZBB));
  mixin (riscv_zbb_instr_mixin(RORI,   I_FORMAT, SHIFT,      RV32ZBB, UIMM));
  mixin (riscv_zbb_instr_mixin(SEXT_B, I_FORMAT, ARITHMETIC, RV32ZBB));
  mixin (riscv_zbb_instr_mixin(SEXT_H, I_FORMAT, ARITHMETIC, RV32ZBB));
  mixin (riscv_zbb_instr_mixin(XNOR,   R_FORMAT, LOGICAL,    RV32ZBB));
  mixin (riscv_zbb_instr_mixin(ZEXT_H, R_FORMAT, ARITHMETIC, RV32ZBB));
 }
 else {
   class riscv_ANDN_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(ANDN,   R_FORMAT, LOGICAL,    RV32ZBB); }
   class riscv_CLZ_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(CLZ,    I_FORMAT, ARITHMETIC, RV32ZBB); }
   class riscv_CPOP_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(CPOP,   I_FORMAT, ARITHMETIC, RV32ZBB); }
   class riscv_CTZ_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(CTZ,    I_FORMAT, ARITHMETIC, RV32ZBB); }
   class riscv_MAX_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(MAX,    R_FORMAT, ARITHMETIC, RV32ZBB); }
   class riscv_MAXU_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(MAXU,   R_FORMAT, ARITHMETIC, RV32ZBB); }
   class riscv_MIN_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(MIN,    R_FORMAT, ARITHMETIC, RV32ZBB); }
   class riscv_MINU_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(MINU,   R_FORMAT, ARITHMETIC, RV32ZBB); }
   class riscv_ORC_B_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(ORC_B,  I_FORMAT, LOGICAL,    RV32ZBB); }
   class riscv_ORN_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(ORN,    R_FORMAT, LOGICAL,    RV32ZBB); }
   class riscv_REV8_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(REV8,   I_FORMAT, SHIFT,      RV32ZBB); }
   class riscv_ROL_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(ROL,    R_FORMAT, SHIFT,      RV32ZBB); }
   class riscv_ROR_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(ROR,    R_FORMAT, SHIFT,      RV32ZBB); }
   class riscv_RORI_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(RORI,   I_FORMAT, SHIFT,      RV32ZBB, UIMM); }
   class riscv_SEXT_B_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(SEXT_B, I_FORMAT, ARITHMETIC, RV32ZBB); }
   class riscv_SEXT_H_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(SEXT_H, I_FORMAT, ARITHMETIC, RV32ZBB); }
   class riscv_XNOR_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(XNOR,   R_FORMAT, LOGICAL,    RV32ZBB); }
   class riscv_ZEXT_H_instr: riscv_zbb_instr
   { mixin RISCV_INSTR_MIXIN!(ZEXT_H, R_FORMAT, ARITHMETIC, RV32ZBB); }
 }
