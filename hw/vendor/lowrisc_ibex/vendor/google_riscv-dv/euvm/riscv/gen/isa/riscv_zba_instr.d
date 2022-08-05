/*
 * Copyright 2018 Google LLC
 * Copyright 2021 Silicon Labs, Inc.
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
module riscv.gen.isa.riscv_zba_instr;

import riscv.gen.riscv_instr_pkg: riscv_instr_group_t, riscv_instr_name_t;
import riscv.gen.isa.riscv_instr: riscv_instr;
import riscv.gen.target: XLEN;
import riscv.gen.riscv_instr_gen_config: riscv_instr_gen_config;
import riscv.gen.target: supported_isa;

import std.format: format;

import esdl.data.bvec: ubvec, toubvec, clog2;
import uvm;

import std.algorithm: canFind;

class riscv_zba_instr: riscv_instr
{
  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  override void pre_randomize() {
    super.pre_randomize();
  }

  override void set_imm_len() {
    if (instr_name != riscv_instr_name_t.SLLI_UW) {
      imm_len = toubvec!5(clog2(XLEN) - 1);
    }
    else {
      imm_len = toubvec!5(clog2(XLEN));
    }
    imm_mask = imm_mask << imm_len;
  }

  override ubvec!7 get_opcode() {
    switch (instr_name) {
    case riscv_instr_name_t.SH1ADD,
      riscv_instr_name_t.SH2ADD,
      riscv_instr_name_t.SH3ADD:     return toubvec!7(0b0110011);
    case riscv_instr_name_t.SH1ADD_UW,
      riscv_instr_name_t.SH2ADD_UW,
      riscv_instr_name_t.SH3ADD_UW:    return toubvec!7(0b0111011);
    case riscv_instr_name_t.SLLI_UW:   return toubvec!7(0b0011011);
    default:                           return super.get_opcode();
    }
  }

  override ubvec!3 get_func3() {
    switch (instr_name) {
    case riscv_instr_name_t.ADD_UW:    return toubvec!3(0b000);
    case riscv_instr_name_t.SH1ADD:    return toubvec!3(0b010);
    case riscv_instr_name_t.SH2ADD:    return toubvec!3(0b100);
    case riscv_instr_name_t.SH3ADD:    return toubvec!3(0b110);
    case riscv_instr_name_t.SH1ADD_UW: return toubvec!3(0b010);
    case riscv_instr_name_t.SH2ADD_UW: return toubvec!3(0b100);
    case riscv_instr_name_t.SH3ADD_UW: return toubvec!3(0b110);
    case riscv_instr_name_t.SLLI_UW:   return toubvec!3(0b001);
    default:                           return super.get_func3();
    }
  }

  override ubvec!7 get_func7() {
    switch (instr_name) {
    case riscv_instr_name_t.ADD_UW:    return toubvec!7(0b0000100);
    case riscv_instr_name_t.SH1ADD:    return toubvec!7(0b0010000);
    case riscv_instr_name_t.SH2ADD:    return toubvec!7(0b0010000);
    case riscv_instr_name_t.SH3ADD:    return toubvec!7(0b0010000);
    case riscv_instr_name_t.SH1ADD_UW: return toubvec!7(0b0010000);
    case riscv_instr_name_t.SH2ADD_UW: return toubvec!7(0b0010000);
    case riscv_instr_name_t.SH3ADD_UW: return toubvec!7(0b0010000);
    case riscv_instr_name_t.SLLI_UW:   return toubvec!7(0b0010000);
    default:                           return super.get_func7();
    }
  }

  override string convert2bin(string prefix = "") {
    string binary = "";
    if (instr_name == riscv_instr_name_t.SLLI_UW) {
      binary = format("%8h", toubvec!5(0b0_0001) ~ cast(ubvec!7)(imm[0..6]) ~
		      rs1 ~ get_func3() ~ rd ~ get_opcode());
    }
    else {
      binary = super.convert2bin(prefix);
    }
    return binary;
  }

  override bool is_supported(riscv_instr_gen_config cfg) {
    return (cfg.enable_zba_extension &&
	    (supported_isa.canFind(riscv_instr_group_t.RV32ZBA) ||
	     supported_isa.canFind(riscv_instr_group_t.RV64ZBA)) &&
	    [riscv_instr_name_t.ADD_UW, riscv_instr_name_t.SH1ADD,
	     riscv_instr_name_t.SH1ADD_UW, riscv_instr_name_t.SH2ADD,
	     riscv_instr_name_t.SH2ADD_UW, riscv_instr_name_t.SH3ADD,
	     riscv_instr_name_t.SH3ADD_UW, riscv_instr_name_t.SLLI_UW].canFind(instr_name));
  }

}



