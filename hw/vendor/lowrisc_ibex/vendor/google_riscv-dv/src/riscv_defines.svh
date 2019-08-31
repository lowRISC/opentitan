/*
 * Copyright 2018 Google LLC
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

`define add_instr(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
  constraint riscv_``instr_group``_``instr_n``_c { \
    if (instr_name == ``instr_n) { \
        format     == ``instr_format; \
        category   == ``instr_category; \
        group      == ``instr_group; \
        imm_type   == ``imm_tp; \
    } \
  }

`define add_pseudo_instr(instr_n, instr_format, instr_category, instr_group)  \
  constraint riscv_``instr_group``_``instr_n``_c { \
    if (pseudo_instr_name  == ``instr_n) { \
        format             == ``instr_format; \
        category           == ``instr_category; \
        group              == ``instr_group; \
    } \
  }

