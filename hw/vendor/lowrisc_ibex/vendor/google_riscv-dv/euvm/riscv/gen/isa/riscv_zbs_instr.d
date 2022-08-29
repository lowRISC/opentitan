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

module riscv.gen.isa.riscv_zbs_instr;

import riscv.gen.riscv_instr_pkg: riscv_instr_group_t,
  riscv_instr_name_t, riscv_instr_format_t;
import riscv.gen.isa.riscv_instr: riscv_instr;
import riscv.gen.riscv_instr_gen_config: riscv_instr_gen_config;
import riscv.gen.target: supported_isa, XLEN;

import std.format: format;

import esdl.data.bvec: ubvec, toubvec, clog2;
import uvm;

import std.algorithm: canFind;

class riscv_zbs_instr: riscv_instr
{
  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  override void pre_randomize() {
    super.pre_randomize();
  }

  final bool is_rv64() {
    return (group == riscv_instr_group_t.RV64B);
  }

  override void set_imm_len() {
    if (instr_format == riscv_instr_format_t.I_FORMAT) {
      if ([riscv_instr_name_t.BCLRI, riscv_instr_name_t.BEXTI,
	   riscv_instr_name_t.BINVI, riscv_instr_name_t.BSETI].canFind(instr_name)) {
	imm_len = toubvec!5(clog2(XLEN));
      }
    }
    imm_mask = imm_mask << imm_len;
  }

  override ubvec!7 get_opcode() {
    switch (instr_name) {
    case riscv_instr_name_t.BCLR,
      riscv_instr_name_t.BEXT,
      riscv_instr_name_t.BINV,
      riscv_instr_name_t.BSET,
      riscv_instr_name_t.BCLRI,
      riscv_instr_name_t.BEXTI,
      riscv_instr_name_t.BINVI,
      riscv_instr_name_t.BSETI: return toubvec!7(0b0010011);
    default : return super.get_opcode();
    }
  }

  override ubvec!3 get_func3() {
    switch (instr_name) {
    case riscv_instr_name_t.BCLR:  return toubvec!3(0b001);
    case riscv_instr_name_t.BCLRI: return toubvec!3(0b001);
    case riscv_instr_name_t.BEXT:  return toubvec!3(0b101);
    case riscv_instr_name_t.BEXTI: return toubvec!3(0b101);
    case riscv_instr_name_t.BINV:  return toubvec!3(0b001);
    case riscv_instr_name_t.BINVI: return toubvec!3(0b001);
    case riscv_instr_name_t.BSET:  return toubvec!3(0b001);
    case riscv_instr_name_t.BSETI: return toubvec!3(0b001);
    default: return super.get_func3();
    }
  }

  override ubvec!7 get_func7() {
    switch (instr_name) {
    case riscv_instr_name_t.BCLR:  return toubvec!7(0b0100100);
    case riscv_instr_name_t.BCLRI: return toubvec!7(0b0100100);
    case riscv_instr_name_t.BEXT:  return toubvec!7(0b0100100);
    case riscv_instr_name_t.BEXTI: return toubvec!7(0b0100100);
    case riscv_instr_name_t.BINV:  return toubvec!7(0b0110100);
    case riscv_instr_name_t.BINVI: return toubvec!7(0b0110100);
    case riscv_instr_name_t.BSET:  return toubvec!7(0b0010100);
    case riscv_instr_name_t.BSETI: return toubvec!7(0b0010100);
    default : return super.get_func7();
    }
  }

  override string convert2bin(string prefix = "") {
    string binary = "";

    switch (instr_format) {
    case riscv_instr_format_t.I_FORMAT:
      switch (instr_name) {
      case riscv_instr_name_t.BCLRI,
	riscv_instr_name_t.BEXTI,
	riscv_instr_name_t.BINVI,
	riscv_instr_name_t.BSETI:
	binary = format("%8h", (get_func7() | (is_rv64() && imm[5])) ~
			cast (ubvec!6) (imm[0..5]) ~ rs1 ~
			get_func3() ~ rd ~ get_opcode());
	break;
      default: break;
      }
      break;
    default:
      assert (binary == "");
      return super.convert2bin(prefix);
    }
    return binary;
  }

  override bool is_supported(riscv_instr_gen_config cfg) {
    return (cfg.enable_zbs_extension &&
	    (supported_isa.canFind(riscv_instr_group_t.RV32ZBS) ||
	     supported_isa.canFind(riscv_instr_group_t.RV64ZBS)) &&
	    [riscv_instr_name_t.BCLR, riscv_instr_name_t.BEXT,
	     riscv_instr_name_t.BINV, riscv_instr_name_t.BSET,
	     riscv_instr_name_t.BCLRI, riscv_instr_name_t.BEXTI,
	     riscv_instr_name_t.BINVI, riscv_instr_name_t.BSETI].canFind(instr_name));
  }
}
