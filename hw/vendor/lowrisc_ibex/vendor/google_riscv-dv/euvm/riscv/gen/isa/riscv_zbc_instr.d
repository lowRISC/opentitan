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
module riscv.gen.isa.riscv_zbc_instr;

import riscv.gen.riscv_instr_pkg: riscv_instr_group_t, riscv_instr_name_t;
import riscv.gen.isa.riscv_instr: riscv_instr;
import riscv.gen.riscv_instr_gen_config: riscv_instr_gen_config;
import riscv.gen.target: supported_isa;

import std.format: format;

import esdl.data.bvec: ubvec, toubvec, clog2;
import uvm;

import std.algorithm: canFind;

class riscv_zbc_instr: riscv_instr
{
  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  override void pre_randomize() {
    super.pre_randomize();
  }

  override ubvec!7 get_opcode() {
    switch (instr_name) {
    case riscv_instr_name_t.CLMUL,
      riscv_instr_name_t.CLMULH,
      riscv_instr_name_t.CLMULR: return toubvec!7(0b011_0011);
    default:                     return super.get_opcode();
    }
  }

  override ubvec!3 get_func3() {
    switch (instr_name) {
    case riscv_instr_name_t.CLMUL:  return toubvec!3(0b001);
    case riscv_instr_name_t.CLMULH: return toubvec!3(0b011);
    case riscv_instr_name_t.CLMULR: return toubvec!3(0b010);
    default:                        return super.get_func3();
    }
  }

  override ubvec!7 get_func7() {
    switch (instr_name) {
    case riscv_instr_name_t.CLMUL:  return toubvec!7(0b000_0101);
    case riscv_instr_name_t.CLMULH: return toubvec!7(0b000_0101);
    case riscv_instr_name_t.CLMULR: return toubvec!7(0b000_0101);
    default:                        return super.get_func7();
    }
  }

  override string convert2bin(string prefix = "") {
    string binary = "";
    if ([riscv_instr_name_t.CLMUL, riscv_instr_name_t.CLMULH,
	 riscv_instr_name_t.CLMULR].canFind(instr_name)) {
      binary = format("%8h", get_func7() ~ rs2 ~ rs1 ~ get_func3() ~ rd ~ get_opcode());
    }
    else {
      binary = super.convert2bin(prefix);
    }
    return binary;
  }

  override bool is_supported(riscv_instr_gen_config cfg) {
    return (cfg.enable_zbc_extension &&
	    (supported_isa.canFind(riscv_instr_group_t.RV32ZBC) ||
	     supported_isa.canFind(riscv_instr_group_t.RV64ZBC)) &&
	    [riscv_instr_name_t.CLMUL, riscv_instr_name_t.CLMULH,
	     riscv_instr_name_t.CLMULR].canFind(instr_name));
  }
}
