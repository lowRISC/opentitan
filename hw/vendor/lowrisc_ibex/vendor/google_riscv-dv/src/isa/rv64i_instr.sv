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

`DEFINE_INSTR(LWU,     I_FORMAT, LOAD, RV64I)
`DEFINE_INSTR(LD,      I_FORMAT, LOAD, RV64I)
`DEFINE_INSTR(SD,      S_FORMAT, STORE, RV64I)
// SHIFT intructions
`DEFINE_INSTR(SLLW,    R_FORMAT, SHIFT, RV64I)
`DEFINE_INSTR(SLLIW,   I_FORMAT, SHIFT, RV64I)
`DEFINE_INSTR(SRLW,    R_FORMAT, SHIFT, RV64I)
`DEFINE_INSTR(SRLIW,   I_FORMAT, SHIFT, RV64I)
`DEFINE_INSTR(SRAW,    R_FORMAT, SHIFT, RV64I)
`DEFINE_INSTR(SRAIW,   I_FORMAT, SHIFT, RV64I)
// ARITHMETIC intructions
`DEFINE_INSTR(ADDW,    R_FORMAT, ARITHMETIC, RV64I)
`DEFINE_INSTR(ADDIW,   I_FORMAT, ARITHMETIC, RV64I)
`DEFINE_INSTR(SUBW,    R_FORMAT, ARITHMETIC, RV64I)
