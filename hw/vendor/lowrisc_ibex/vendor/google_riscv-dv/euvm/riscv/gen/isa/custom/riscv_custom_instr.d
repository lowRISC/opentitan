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

// Custom instruction class

module riscv.gen.isa.custom.riscv_custom_instr;

import riscv.gen.riscv_instr_pkg: riscv_instr_group_t,
  riscv_instr_name_t, MAX_INSTR_STR_LEN, riscv_fpr_t,
  riscv_instr_format_t, riscv_instr_category_t,
  format_string, f_rounding_mode_t;
import riscv.gen.isa.riscv_instr: riscv_instr;
import std.string: toUpper, toLower;
import std.format: format;
import std.algorithm: canFind;

import esdl.rand: rand;
import esdl.data.bvec: ubvec;
import uvm;

class riscv_custom_instr: riscv_instr
{
  // TODO: Add custom operands here, example:
  // rand riscv_reg_t rs3;

  mixin uvm_object_utils;
  this(string name = "") {
    super(name);
  }

  override string get_instr_name() {
    import std.conv: to;
    return instr_name.to!string();
    // TODO: Add custom instruction name encoding here
  }

  // Convert the instruction to assembly code
  override string convert2asm(string prefix = "") {
    string asm_str;
    asm_str = format_string("nop", MAX_INSTR_STR_LEN);
    /* TODO: Convert custom instruction to assembly format. Example:
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    case (instr_name)
      CUSTOM_1: asm_str = $sformatf("%0s %0s, (%0s)", asm_str, rd.name(), rs1.name());
      CUSTOM_2: asm_str = $sformatf("%0s %0s", asm_str, r3.name());
    endcase
    */
    comment = get_instr_name() ~ " " ~ comment;
    if (comment != "") {
      asm_str ~= " #" ~ comment;
    }
    return asm_str.toLower();
  }
}
