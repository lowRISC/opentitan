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

`define INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM) \
    static bit valid = riscv_instr::register(instr_n);  \
    `uvm_object_utils(riscv_``instr_n``_instr)  \
    function new(string name = "");  \
      super.new(name);  \
      this.instr_name = ``instr_n; \
      this.format = ``instr_format;  \
      this.group = ``instr_group;  \
      this.category = ``instr_category;  \
      this.imm_type = ``imm_tp;  \
      set_imm_len(); \
      set_rand_mode(); \
    endfunction \
  endclass

 `define VA_INSTR_BODY(instr_n, instr_format, instr_category, instr_group, vav, ext = "") \
    static bit valid = riscv_instr::register(instr_n);  \
    `uvm_object_utils(riscv_``instr_n``_instr)  \
    function new(string name = "");  \
      super.new(name);  \
      this.instr_name = ``instr_n; \
      this.format = ``instr_format;  \
      this.group = ``instr_group;  \
      this.category = ``instr_category;  \
      this.imm_type = IMM;  \
      this.allowed_va_variants = ``vav; \
      this.sub_extension = ``ext; \
      set_imm_len(); \
      set_rand_mode(); \
    endfunction \
  endclass

// Regular integer instruction
`define DEFINE_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
  class riscv_``instr_n``_instr extends riscv_instr;  \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

// Floating point instruction
`define DEFINE_FP_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
  class riscv_``instr_n``_instr extends riscv_floating_point_instr;  \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

// A-extension instruction
`define DEFINE_AMO_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
  class riscv_``instr_n``_instr extends riscv_amo_instr;  \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

// Compressed instruction
`define DEFINE_C_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
  class riscv_``instr_n``_instr extends riscv_compressed_instr;  \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

// Floating point compressed instruction
`define DEFINE_FC_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
  class riscv_``instr_n``_instr extends riscv_compressed_instr;  \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

// Vector arithmetic instruction
`define DEFINE_VA_INSTR(instr_n, instr_format, instr_category, instr_group, vav = {}, ext = "")\
  class riscv_``instr_n``_instr extends riscv_vector_instr;  \
    `VA_INSTR_BODY(instr_n, instr_format, instr_category, instr_group, vav, ext)

// Custom extension instruction
`define DEFINE_CUSTOM_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
  class riscv_``instr_n``_instr extends riscv_custom_instr;  \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

//B-extension instruction
`define DEFINE_B_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
  class riscv_``instr_n``_instr extends riscv_b_instr;  \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

