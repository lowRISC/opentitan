/*
 * Copyright 2019 Google LLC
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

// Psuedo instructions are used to simplify assembly program writing
module riscv.gen.riscv_pseudo_instr;

import riscv.gen.riscv_instr_pkg: riscv_pseudo_instr_name_t, riscv_instr_format_t,
  riscv_instr_category_t, riscv_instr_group_t, format_string, MAX_INSTR_STR_LEN;
import riscv.gen.isa.riscv_instr: riscv_instr;

import std.format: format;
import std.string: toLower;

import esdl.rand: rand, constraint;
import uvm;

class riscv_pseudo_instr: riscv_instr
{
  @rand riscv_pseudo_instr_name_t  pseudo_instr_name;

  // `add_pseudo_instr(LI, I_FORMAT, LOAD, RV32I)
  constraint! q{
    if (pseudo_instr_name  == riscv_pseudo_instr_name_t.LI) {
      instr_format       == riscv_instr_format_t.I_FORMAT;
      category           == riscv_instr_category_t.LOAD;
      group              == riscv_instr_group_t.RV32I;
    }
  } riscv_RV32I_LI_c;

  // `add_pseudo_instr(LA, I_FORMAT, LOAD, RV32I)
  constraint! q{
    if (pseudo_instr_name  == riscv_pseudo_instr_name_t.LA) {
      instr_format       == riscv_instr_format_t.I_FORMAT;
      category           == riscv_instr_category_t.LOAD;
      group              == riscv_instr_group_t.RV32I;
    }
  } riscv_RV32I_LA_c;

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
    process_load_store = false;
    this.instr_format = riscv_instr_format_t.I_FORMAT;
  }

  // Convert the instruction to assembly code
  override string convert2asm(string prefix = "") {
    string asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    // instr rd,imm
    asm_str = format("%0s%0s, %0s", asm_str, rd, get_imm());
    if (comment != "")
      asm_str ~= " #"~comment;
    return asm_str.toLower();
  }

  override string get_instr_name() {
    import std.conv: to;
    return pseudo_instr_name.to!string();
  }

}
