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

`DEFINE_C_INSTR(C_ADDIW,  CI_FORMAT, ARITHMETIC, RV64C)
`DEFINE_C_INSTR(C_SUBW,   CA_FORMAT, ARITHMETIC, RV64C)
`DEFINE_C_INSTR(C_ADDW,   CA_FORMAT, ARITHMETIC, RV64C)
`DEFINE_C_INSTR(C_LD,     CL_FORMAT, LOAD, RV64C, UIMM)
`DEFINE_C_INSTR(C_SD,     CS_FORMAT, STORE, RV64C, UIMM)
`DEFINE_C_INSTR(C_LDSP,   CI_FORMAT, LOAD, RV64C, UIMM)
`DEFINE_C_INSTR(C_SDSP,   CSS_FORMAT, STORE, RV64C, UIMM)
