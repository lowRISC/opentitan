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

`DEFINE_AMO_INSTR(LR_W,      R_FORMAT, LOAD, RV32A)
`DEFINE_AMO_INSTR(SC_W,      R_FORMAT, STORE, RV32A)
`DEFINE_AMO_INSTR(AMOSWAP_W, R_FORMAT, AMO, RV32A)
`DEFINE_AMO_INSTR(AMOADD_W,  R_FORMAT, AMO, RV32A)
`DEFINE_AMO_INSTR(AMOAND_W,  R_FORMAT, AMO, RV32A)
`DEFINE_AMO_INSTR(AMOOR_W,   R_FORMAT, AMO, RV32A)
`DEFINE_AMO_INSTR(AMOXOR_W,  R_FORMAT, AMO, RV32A)
`DEFINE_AMO_INSTR(AMOMIN_W,  R_FORMAT, AMO, RV32A)
`DEFINE_AMO_INSTR(AMOMAX_W,  R_FORMAT, AMO, RV32A)
`DEFINE_AMO_INSTR(AMOMINU_W, R_FORMAT, AMO, RV32A)
`DEFINE_AMO_INSTR(AMOMAXU_W, R_FORMAT, AMO, RV32A)
