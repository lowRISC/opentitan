/*
 * Copyright 2019 Google LLC
 * Copyright 2019 Mellanox Technologies Ltd
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

// Remaining bitmanip instructions of draft v.0.93 not ratified in v.1.00 (Zba, Zbb, Zbc, Zbs).

// ARITHMETIC intructions
`DEFINE_B_INSTR(BMATOR,       R_FORMAT, ARITHMETIC, RV64B)
`DEFINE_B_INSTR(BMATXOR,      R_FORMAT, ARITHMETIC, RV64B)
`DEFINE_B_INSTR(BMATFLIP,     R_FORMAT, ARITHMETIC, RV64B)
`DEFINE_B_INSTR(CRC32_D,      R_FORMAT, ARITHMETIC, RV64B)
`DEFINE_B_INSTR(CRC32C_D,     R_FORMAT, ARITHMETIC, RV64B)
`DEFINE_B_INSTR(SHFLW,        R_FORMAT, ARITHMETIC, RV64B)
`DEFINE_B_INSTR(UNSHFLW,      R_FORMAT, ARITHMETIC, RV64B)
`DEFINE_B_INSTR(BCOMPRESSW,   R_FORMAT, ARITHMETIC, RV64B)
`DEFINE_B_INSTR(BDECOMPRESSW, R_FORMAT, ARITHMETIC, RV64B)
`DEFINE_B_INSTR(BFPW,         R_FORMAT, ARITHMETIC, RV64B)
// SHIFT intructions
`DEFINE_B_INSTR(SLOW,    R_FORMAT, SHIFT, RV64B)
`DEFINE_B_INSTR(SROW,    R_FORMAT, SHIFT, RV64B)
`DEFINE_B_INSTR(SLOIW,   I_FORMAT, SHIFT, RV64B, UIMM)
`DEFINE_B_INSTR(SROIW,   I_FORMAT, SHIFT, RV64B, UIMM)
`DEFINE_B_INSTR(GREVW,   R_FORMAT, SHIFT, RV64B)
`DEFINE_B_INSTR(GREVIW,  I_FORMAT, SHIFT, RV64B, UIMM)
`DEFINE_B_INSTR(FSLW,   R4_FORMAT, SHIFT, RV64B)
`DEFINE_B_INSTR(FSRW,   R4_FORMAT, SHIFT, RV64B)
`DEFINE_B_INSTR(FSRIW,   I_FORMAT, SHIFT, RV64B, UIMM)
// LOGICAL instructions
`DEFINE_B_INSTR(GORCW,   R_FORMAT, LOGICAL, RV64B)
`DEFINE_B_INSTR(GORCIW,  I_FORMAT, LOGICAL, RV64B, UIMM)
`DEFINE_B_INSTR(PACKW,   R_FORMAT, LOGICAL, RV64B)
`DEFINE_B_INSTR(PACKUW,  R_FORMAT, LOGICAL, RV64B)
`DEFINE_B_INSTR(XPERM_W, R_FORMAT, LOGICAL, RV64B)
