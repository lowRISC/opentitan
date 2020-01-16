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

`DEFINE_FP_INSTR(FMV_X_D,   I_FORMAT, ARITHMETIC, RV64D)
`DEFINE_FP_INSTR(FMV_D_X,   I_FORMAT, ARITHMETIC, RV64D)
`DEFINE_FP_INSTR(FCVT_L_D,  I_FORMAT, ARITHMETIC, RV64D)
`DEFINE_FP_INSTR(FCVT_LU_D, I_FORMAT, ARITHMETIC, RV64D)
`DEFINE_FP_INSTR(FCVT_D_L,  I_FORMAT, ARITHMETIC, RV64D)
`DEFINE_FP_INSTR(FCVT_D_LU, I_FORMAT, ARITHMETIC, RV64D)
