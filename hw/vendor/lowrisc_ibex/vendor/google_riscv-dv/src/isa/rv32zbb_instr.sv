/*
 * Copyright 2018 Google LLC
 * Copyright 2021 Silicon Labs, Inc.
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

`DEFINE_ZBB_INSTR(ANDN,   R_FORMAT, LOGICAL,    RV32ZBB);
`DEFINE_ZBB_INSTR(CLZ,    I_FORMAT, ARITHMETIC, RV32ZBB);
`DEFINE_ZBB_INSTR(CPOP,   I_FORMAT, ARITHMETIC, RV32ZBB);
`DEFINE_ZBB_INSTR(CTZ,    I_FORMAT, ARITHMETIC, RV32ZBB);
`DEFINE_ZBB_INSTR(MAX,    R_FORMAT, ARITHMETIC, RV32ZBB);
`DEFINE_ZBB_INSTR(MAXU,   R_FORMAT, ARITHMETIC, RV32ZBB);
`DEFINE_ZBB_INSTR(MIN,    R_FORMAT, ARITHMETIC, RV32ZBB);
`DEFINE_ZBB_INSTR(MINU,   R_FORMAT, ARITHMETIC, RV32ZBB);
`DEFINE_ZBB_INSTR(ORC_B,  I_FORMAT, LOGICAL,    RV32ZBB);
`DEFINE_ZBB_INSTR(ORN,    R_FORMAT, LOGICAL,    RV32ZBB);
`DEFINE_ZBB_INSTR(REV8,   I_FORMAT, SHIFT,      RV32ZBB);
`DEFINE_ZBB_INSTR(ROL,    R_FORMAT, SHIFT,      RV32ZBB);
`DEFINE_ZBB_INSTR(ROR,    R_FORMAT, SHIFT,      RV32ZBB);
`DEFINE_ZBB_INSTR(RORI,   I_FORMAT, SHIFT,      RV32ZBB, UIMM);
`DEFINE_ZBB_INSTR(SEXT_B, I_FORMAT, ARITHMETIC, RV32ZBB);
`DEFINE_ZBB_INSTR(SEXT_H, I_FORMAT, ARITHMETIC, RV32ZBB);
`DEFINE_ZBB_INSTR(XNOR,   R_FORMAT, LOGICAL,    RV32ZBB);
`DEFINE_ZBB_INSTR(ZEXT_H, R_FORMAT, ARITHMETIC, RV32ZBB);
