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

module riscv.gen.isa.riscv_amo_instr;

import riscv.gen.riscv_instr_pkg: riscv_instr_group_t, format_string,
  riscv_instr_name_t, MAX_INSTR_STR_LEN;
import riscv.gen.isa.riscv_instr: riscv_instr;
import std.format: format;

import esdl.rand: constraint, rand;

import uvm;

class riscv_amo_instr: riscv_instr
{
  mixin uvm_object_utils;

  @rand bool aq;
  @rand bool rl;

  constraint! q{
    (aq && rl) == false;
  } aq_rl_c;


  this(string name = "") {
    super(name);
  }

  override string get_instr_name() {
    import std.conv: to;
    string instr_name_str = instr_name.to!string();
    if (group == riscv_instr_group_t.RV32A) {
      instr_name_str  = instr_name_str[0..$ - 2] ~ ".w";
      instr_name_str = aq ? instr_name_str ~ ".aq" :
	rl ? instr_name_str ~ ".rl" : instr_name_str;
    }
    else if (group == riscv_instr_group_t.RV64A) {
      instr_name_str = instr_name_str[0..$ - 2] ~ ".d";
      instr_name_str = aq ? instr_name_str ~ ".aq" :
	rl ? instr_name_str ~ ".rl" : instr_name_str;
    }
    else {
      uvm_fatal(get_full_name(), format("Unexpected amo instr group: %0s / %0s",
					group, instr_name));
    }
    return instr_name_str;
  }

  // Convert the instruction to assembly code
  override string convert2asm(string prefix = "") {
    import std.string: toLower;
    string asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    if (group.inside(riscv_instr_group_t.RV32A, riscv_instr_group_t.RV64A))  {
      if (instr_name.inside(riscv_instr_name_t.LR_W, riscv_instr_name_t.LR_D)) {
        asm_str = format("%0s %0s, (%0s)", asm_str, rd, rs1);
      }
      else {
        asm_str = format("%0s %0s, %0s, (%0s)", asm_str, rd, rs2, rs1);
      }
    }
    else {
      uvm_fatal(get_full_name(), format("Unexpected amo instr group: %0s / %0s",
					group, instr_name));
    }
    if(comment != "")
      asm_str ~= " #" ~ comment;
    return asm_str.toLower();
  }

  override void do_copy(uvm_object rhs) {
    super.copy(rhs);
    riscv_amo_instr rhs_ = cast(riscv_amo_instr) rhs;
    assert (rhs_ !is null);
    this.aq = rhs_.aq;
    this.rl = rhs_.rl;
  }
}
