/*
 * Copyright 2019 Google LLC
 * Copyright 2019 Mellanox Technologies Ltd
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

module riscv.gen.isa.riscv_b_instr;

import riscv.gen.riscv_instr_pkg: riscv_reg_t, riscv_instr_name_t, b_ext_group_t,
  riscv_instr_category_t, riscv_instr_format_t, riscv_instr_group_t,
  MAX_INSTR_STR_LEN, format_string;
import riscv.gen.target: XLEN;
import riscv.gen.riscv_instr_gen_config: riscv_instr_gen_config;
import riscv.gen.isa.riscv_instr: riscv_instr;
import std.format: format;

import esdl.rand: rand;
import esdl.data.bvec: ubvec, toubvec, clog2;
import std.algorithm: canFind;

import std.string: toLower;

import uvm;

class riscv_b_instr: riscv_instr
{
  mixin uvm_object_utils;

  @rand riscv_reg_t rs3;
  bool has_rs3 = false;


  this(string name = "") {
    super(name);
  }

  override void set_rand_mode() {
    super.set_rand_mode();
    has_rs3 = false;
    switch (instr_format) {
    case riscv_instr_format_t.R_FORMAT:
      if ([riscv_instr_name_t.BMATFLIP, riscv_instr_name_t.CRC32_B,
	   riscv_instr_name_t.CRC32_H,  riscv_instr_name_t.CRC32_W,
	   riscv_instr_name_t.CRC32C_B, riscv_instr_name_t.CRC32C_H,
	   riscv_instr_name_t.CRC32C_W, riscv_instr_name_t.CRC32_D,
	   riscv_instr_name_t.CRC32C_D].canFind(instr_name)) {
	has_rs2 = false;
      }
      break;
    case riscv_instr_format_t.R4_FORMAT:
        has_imm = false;
        has_rs3 = true;
	break;
    case riscv_instr_format_t.I_FORMAT:
      has_rs2 = false;
      if ([riscv_instr_name_t.FSRI,
	   riscv_instr_name_t.FSRIW].canFind(instr_name)) {
	has_rs3 = true;
      }
      break;
    default: break;
    }
  }

  override void pre_randomize() {
    super.pre_randomize();
    rand_mode!q{rs3}(has_rs3);
  }

  override void set_imm_len() {

    if ([riscv_instr_format_t.I_FORMAT].canFind(instr_format)) {
      if ([riscv_instr_category_t.SHIFT,
	   riscv_instr_category_t.LOGICAL].canFind(category)) {
	imm_len = toubvec!5(clog2(XLEN));
      }
      // ARITHMETIC RV32B
      if ([riscv_instr_name_t.SHFLI,
	   riscv_instr_name_t.UNSHFLI].canFind(instr_name)) {
        imm_len = toubvec!5(clog2(XLEN) - 1);
      }
    }

    imm_mask <<= imm_len;
  }

  // Convert the instruction to assembly code
  override string convert2asm(string prefix = "") {
    string asm_str_final, asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);

    switch (instr_format) {
    case riscv_instr_format_t.I_FORMAT:
      if ([riscv_instr_name_t.FSRI,
	   riscv_instr_name_t.FSRIW].canFind(instr_name)) {  // instr rd,rs1,rs3,imm
	asm_str_final = format("%0s%0s, %0s, %0s, %0s", asm_str, rd, rs1,
			       rs3, get_imm());
      }
      break;
    case riscv_instr_format_t.R_FORMAT:  //instr rd rs1
      if (! has_rs2) {
	asm_str_final = format("%0s%0s, %0s", asm_str, rd, rs1);
      }
      break;
    case riscv_instr_format_t.R4_FORMAT: // instr rd,rs1,rs2,rs3
      asm_str_final = format("%0s%0s, %0s, %0s, %0s", asm_str, rd, rs1,
			     rs2, rs3);
      break;
    default: uvm_info(get_full_name(), format("Unsupported format %0s", instr_format), UVM_LOW);
    }

    if (asm_str_final == "") {
      return super.convert2asm(prefix);
    }

    if (comment != "") asm_str_final ~= " #" ~ comment;
    return asm_str_final.toLower();
  }

  override ubvec!7 get_opcode() {
    switch (instr_name) {
    case riscv_instr_name_t.GORC,
      riscv_instr_name_t.SLO,
      riscv_instr_name_t.SRO,
      riscv_instr_name_t.GREV,
      riscv_instr_name_t.XPERM_N,
      riscv_instr_name_t.XPERM_B,
      riscv_instr_name_t.XPERM_H,
      riscv_instr_name_t.XPERM_W: return toubvec!7(0b0110011);
    case riscv_instr_name_t.GORCI,
      riscv_instr_name_t.SLOI,
      riscv_instr_name_t.SROI,
      riscv_instr_name_t.GREVI,
      riscv_instr_name_t.CMIX,
      riscv_instr_name_t.CMOV,
      riscv_instr_name_t.FSL: return toubvec!7(0b0010011);
    case riscv_instr_name_t.FSR,
      riscv_instr_name_t.FSRI,
      riscv_instr_name_t.BMATFLIP,
      riscv_instr_name_t.CRC32_B,
      riscv_instr_name_t.CRC32_H,
      riscv_instr_name_t.CRC32_W,
      riscv_instr_name_t.CRC32C_B,
      riscv_instr_name_t.CRC32C_H: return toubvec!7(0b0010011);
    case riscv_instr_name_t.CRC32C_W,
      riscv_instr_name_t.CRC32_D,
      riscv_instr_name_t.CRC32C_D: return toubvec!7(0b0010011);
    case riscv_instr_name_t.SHFL,
      riscv_instr_name_t.UNSHFL,
      riscv_instr_name_t.BCOMPRESS,
      riscv_instr_name_t.BDECOMPRESS,
      riscv_instr_name_t.PACK,
      riscv_instr_name_t.PACKU,
      riscv_instr_name_t.BMATOR,
      riscv_instr_name_t.BMATXOR,
      riscv_instr_name_t.PACKH,
      riscv_instr_name_t.BFP: return toubvec!7(0b0110011);
    case riscv_instr_name_t.SHFLI,
      riscv_instr_name_t.UNSHFLI: return toubvec!7(0b0010011);
    case riscv_instr_name_t.SLOW,
      riscv_instr_name_t.SROW,
      riscv_instr_name_t.GORCW,
      riscv_instr_name_t.GREVW: return toubvec!7(0b0111011);
    case riscv_instr_name_t.SLOIW,
      riscv_instr_name_t.SROIW,
      riscv_instr_name_t.GORCIW,
      riscv_instr_name_t.GREVIW: return toubvec!7(0b0011011);
    case riscv_instr_name_t.FSLW,
      riscv_instr_name_t.FSRW: return toubvec!7(0b0111011);
    case riscv_instr_name_t.FSRIW: return toubvec!7(0b0011011);
    case riscv_instr_name_t.SHFLW,
      riscv_instr_name_t.UNSHFLW,
      riscv_instr_name_t.BCOMPRESSW,
      riscv_instr_name_t.BDECOMPRESSW,
      riscv_instr_name_t.PACKW,
      riscv_instr_name_t.PACKUW,
      riscv_instr_name_t.BFPW: return toubvec!7(0b0111011);
    default:                   return super.get_opcode();
    }
  }

  override ubvec!3 get_func3() {
    switch (instr_name) {
    case riscv_instr_name_t.GORC: return toubvec!3(0b101);
    case riscv_instr_name_t.GORCI: return toubvec!3(0b101);
    case riscv_instr_name_t.SLO: return toubvec!3(0b001);
    case riscv_instr_name_t.SRO: return toubvec!3(0b101);
    case riscv_instr_name_t.SLOI: return toubvec!3(0b001);
    case riscv_instr_name_t.SROI: return toubvec!3(0b101);
    case riscv_instr_name_t.GREV: return toubvec!3(0b101);
    case riscv_instr_name_t.GREVI: return toubvec!3(0b101);
    case riscv_instr_name_t.CMIX: return toubvec!3(0b001);
    case riscv_instr_name_t.CMOV: return toubvec!3(0b101);
    case riscv_instr_name_t.FSL: return toubvec!3(0b001);
    case riscv_instr_name_t.FSR: return toubvec!3(0b101);
    case riscv_instr_name_t.FSRI: return toubvec!3(0b101);
    case riscv_instr_name_t.BMATFLIP: return toubvec!3(0b001);
    case riscv_instr_name_t.CRC32_B: return toubvec!3(0b001);
    case riscv_instr_name_t.CRC32_H: return toubvec!3(0b001);
    case riscv_instr_name_t.CRC32_W: return toubvec!3(0b001);
    case riscv_instr_name_t.CRC32C_B: return toubvec!3(0b001);
    case riscv_instr_name_t.CRC32C_H: return toubvec!3(0b001);
    case riscv_instr_name_t.CRC32C_W: return toubvec!3(0b001);
    case riscv_instr_name_t.CRC32_D: return toubvec!3(0b001);
    case riscv_instr_name_t.CRC32C_D: return toubvec!3(0b001);
    case riscv_instr_name_t.SHFL: return toubvec!3(0b001);
    case riscv_instr_name_t.UNSHFL: return toubvec!3(0b101);
    case riscv_instr_name_t.BCOMPRESS: return toubvec!3(0b110);
    case riscv_instr_name_t.BDECOMPRESS: return toubvec!3(0b110);
    case riscv_instr_name_t.PACK: return toubvec!3(0b100);
    case riscv_instr_name_t.PACKU: return toubvec!3(0b100);
    case riscv_instr_name_t.BMATOR: return toubvec!3(0b011);
    case riscv_instr_name_t.BMATXOR: return toubvec!3(0b011);
    case riscv_instr_name_t.PACKH: return toubvec!3(0b111);
    case riscv_instr_name_t.BFP: return toubvec!3(0b111);
    case riscv_instr_name_t.SHFLI: return toubvec!3(0b001);
    case riscv_instr_name_t.UNSHFLI: return toubvec!3(0b101);
    case riscv_instr_name_t.SLOW: return toubvec!3(0b001);
    case riscv_instr_name_t.SROW: return toubvec!3(0b101);
    case riscv_instr_name_t.ROLW: return toubvec!3(0b001);
    case riscv_instr_name_t.GORCW: return toubvec!3(0b101);
    case riscv_instr_name_t.GREVW: return toubvec!3(0b101);
    case riscv_instr_name_t.SLOIW: return toubvec!3(0b001);
    case riscv_instr_name_t.SROIW: return toubvec!3(0b101);
    case riscv_instr_name_t.RORIW: return toubvec!3(0b101);
    case riscv_instr_name_t.GORCIW: return toubvec!3(0b101);
    case riscv_instr_name_t.GREVIW: return toubvec!3(0b101);
    case riscv_instr_name_t.FSLW: return toubvec!3(0b001);
    case riscv_instr_name_t.FSRW: return toubvec!3(0b101);
    case riscv_instr_name_t.FSRIW: return toubvec!3(0b101);
    case riscv_instr_name_t.SHFLW: return toubvec!3(0b001);
    case riscv_instr_name_t.UNSHFLW: return toubvec!3(0b101);
    case riscv_instr_name_t.BCOMPRESSW: return toubvec!3(0b110);
    case riscv_instr_name_t.BDECOMPRESSW: return toubvec!3(0b110);
    case riscv_instr_name_t.PACKW: return toubvec!3(0b100);
    case riscv_instr_name_t.PACKUW: return toubvec!3(0b100);
    case riscv_instr_name_t.BFPW: return toubvec!3(0b111);
    case riscv_instr_name_t.XPERM_N: return toubvec!3(0b010);
    case riscv_instr_name_t.XPERM_B: return toubvec!3(0b100);
    case riscv_instr_name_t.XPERM_H: return toubvec!3(0b110);
    case riscv_instr_name_t.XPERM_W: return toubvec!3(0b000);
    default:                         return super.get_func3();
    }
  }

  override ubvec!7 get_func7() {
    switch (instr_name) {
    case riscv_instr_name_t.ANDN: return toubvec!7(0b0100000);
    case riscv_instr_name_t.ORN: return toubvec!7(0b0100000);
    case riscv_instr_name_t.XNOR: return toubvec!7(0b0100000);
    case riscv_instr_name_t.GORC: return toubvec!7(0b0010100);
    case riscv_instr_name_t.SLO: return toubvec!7(0b0010000);
    case riscv_instr_name_t.SRO: return toubvec!7(0b0010000);
    case riscv_instr_name_t.ROL: return toubvec!7(0b0110000);
    case riscv_instr_name_t.ROR: return toubvec!7(0b0110000);
    case riscv_instr_name_t.GREV: return toubvec!7(0b0110100);
    case riscv_instr_name_t.BMATFLIP: return toubvec!7(0b0110000);
    case riscv_instr_name_t.CRC32_B: return toubvec!7(0b0110000);
    case riscv_instr_name_t.CRC32_H: return toubvec!7(0b0110000);
    case riscv_instr_name_t.CRC32_W: return toubvec!7(0b0110000);
    case riscv_instr_name_t.CRC32C_B: return toubvec!7(0b0110000);
    case riscv_instr_name_t.CRC32C_H: return toubvec!7(0b0110000);
    case riscv_instr_name_t.CRC32C_W: return toubvec!7(0b0110000);
    case riscv_instr_name_t.CRC32_D: return toubvec!7(0b0110000);
    case riscv_instr_name_t.CRC32C_D: return toubvec!7(0b0110000);
    case riscv_instr_name_t.SHFL: return toubvec!7(0b0000100);
    case riscv_instr_name_t.UNSHFL: return toubvec!7(0b0000100);
    case riscv_instr_name_t.BCOMPRESS: return toubvec!7(0b0000100);
    case riscv_instr_name_t.BDECOMPRESS: return toubvec!7(0b0100100);
    case riscv_instr_name_t.PACK: return toubvec!7(0b0000100);
    case riscv_instr_name_t.PACKU: return toubvec!7(0b0100100);
    case riscv_instr_name_t.BMATOR: return toubvec!7(0b0000100);
    case riscv_instr_name_t.BMATXOR: return toubvec!7(0b0100100);
    case riscv_instr_name_t.PACKH: return toubvec!7(0b0000100);
    case riscv_instr_name_t.BFP: return toubvec!7(0b0100100);
    case riscv_instr_name_t.SLOW: return toubvec!7(0b0010000);
    case riscv_instr_name_t.SROW: return toubvec!7(0b0010000);
    case riscv_instr_name_t.GORCW: return toubvec!7(0b0010100);
    case riscv_instr_name_t.GORCIW: return toubvec!7(0b0010100);
    case riscv_instr_name_t.GREVW: return toubvec!7(0b0110100);
    case riscv_instr_name_t.GREVIW: return toubvec!7(0b0110100);
    case riscv_instr_name_t.SLOIW: return toubvec!7(0b0010000);
    case riscv_instr_name_t.SROIW: return toubvec!7(0b0010000);
    case riscv_instr_name_t.SHFLW: return toubvec!7(0b0000100);
    case riscv_instr_name_t.UNSHFLW: return toubvec!7(0b0000100);
    case riscv_instr_name_t.BCOMPRESSW: return toubvec!7(0b0000100);
    case riscv_instr_name_t.BDECOMPRESSW: return toubvec!7(0b0100100);
    case riscv_instr_name_t.PACKW: return toubvec!7(0b0000100);
    case riscv_instr_name_t.PACKUW: return toubvec!7(0b0100100);
    case riscv_instr_name_t.BFPW: return toubvec!7(0b0100100);
    case riscv_instr_name_t.XPERM_N: return toubvec!7(0b0010100);
    case riscv_instr_name_t.XPERM_B: return toubvec!7(0b0010100);
    case riscv_instr_name_t.XPERM_H: return toubvec!7(0b0010100);
    case riscv_instr_name_t.XPERM_W: return toubvec!7(0b0010100);
    default:                         return super.get_func7();
    }
  }

  ubvec!5 get_func5() {
    switch (instr_name) {
    case riscv_instr_name_t.SLOI: return toubvec!5(0b00100);
    case riscv_instr_name_t.SROI: return toubvec!5(0b00100);
    case riscv_instr_name_t.RORI: return toubvec!5(0b01100);
    case riscv_instr_name_t.GORCI: return toubvec!5(0b00101);
    case riscv_instr_name_t.GREVI: return toubvec!5(0b01101);

    case riscv_instr_name_t.CRC32_B: return toubvec!5(0b10000);
    case riscv_instr_name_t.CRC32_H: return toubvec!5(0b10001);
    case riscv_instr_name_t.CRC32_W: return toubvec!5(0b10010);
    case riscv_instr_name_t.CRC32C_B: return toubvec!5(0b11000);
    case riscv_instr_name_t.CRC32C_H: return toubvec!5(0b11001);
    case riscv_instr_name_t.CRC32C_W: return toubvec!5(0b11010);
    case riscv_instr_name_t.CRC32_D: return toubvec!5(0b10011);
    case riscv_instr_name_t.CRC32C_D: return toubvec!5(0b11011);

    case riscv_instr_name_t.BMATFLIP: return toubvec!5(0b00011);
    default: uvm_fatal(get_full_name(), format("Unsupported instruction %0s", instr_name));
      assert (false);
    }
  }

  ubvec!2 get_func2() {
    switch (instr_name) {
    case riscv_instr_name_t.CMIX: return toubvec!2(0b11);
    case riscv_instr_name_t.CMOV: return toubvec!2(0b11);
    case riscv_instr_name_t.FSL: return toubvec!2(0b10);
    case riscv_instr_name_t.FSR: return toubvec!2(0b10);
    case riscv_instr_name_t.FSLW: return toubvec!2(0b10);
    case riscv_instr_name_t.FSRW: return toubvec!2(0b10);
    case riscv_instr_name_t.FSRIW: return toubvec!2(0b10);
    default: uvm_fatal(get_full_name(), format("Unsupported instruction %0s", instr_name));
      assert (false);
    }
  }

  // Convert the instruction to assembly code
  override string convert2bin(string prefix = "") {
    string binary = "";
    switch (instr_format) {
    case riscv_instr_format_t.R_FORMAT:
      if ((category == riscv_instr_category_t.ARITHMETIC) &&
	  (group == riscv_instr_group_t.RV32B)) {
	if ([riscv_instr_name_t.CRC32_B,
	     riscv_instr_name_t.CRC32_H,
	     riscv_instr_name_t.CRC32_W,
	     riscv_instr_name_t.CRC32C_B,
	     riscv_instr_name_t.CRC32C_H,
	     riscv_instr_name_t.CRC32C_W].canFind(instr_name)) {
	  binary =
	    format("%8h", get_func7() ~ get_func5() ~ toubvec!5(rs1) ~ get_func3() ~
		   toubvec!5(rd) ~ get_opcode());
	}
      }

      if ((category == riscv_instr_category_t.ARITHMETIC) &&
	  (group == riscv_instr_group_t.RV64B)) {
	if ([riscv_instr_name_t.CRC32_D,
	     riscv_instr_name_t.CRC32C_D,
	     riscv_instr_name_t.BMATFLIP].canFind(instr_name)) {
	  binary =
	    format("%8h", get_func7() ~ get_func5() ~ toubvec!5(rs1) ~ get_func3() ~
		   toubvec!5(rd) ~ get_opcode());
	}
      }
      break;
    case riscv_instr_format_t.I_FORMAT:
      if (([riscv_instr_category_t.SHIFT,
	    riscv_instr_category_t.LOGICAL].canFind(category)) &&
	  (group == riscv_instr_group_t.RV32B)) {
	binary = format("%8h", get_func5() ~ cast(ubvec!7) imm[0..7] ~ toubvec!5(rs1) ~
			get_func3() ~ toubvec!5(rd) ~ get_opcode());
      }
      else if (([riscv_instr_category_t.SHIFT,
		 riscv_instr_category_t.LOGICAL].canFind(category)) &&
	       (group == riscv_instr_group_t.RV64B)) {
	binary = format("%8h", get_func7() ~ cast(ubvec!5) imm[0..5] ~ toubvec!5(rs1) ~
			get_func3() ~ toubvec!5(rd) ~ get_opcode());
      }

      if ([riscv_instr_name_t.FSRI].canFind(instr_name)) {
	binary = format("%8h", toubvec!5(rs3) ~ toubvec!1(0b1) ~ cast(ubvec!6) imm[0..6] ~
			toubvec!5(rs1) ~ get_func3() ~ toubvec!5(rd) ~ get_opcode());
      }

      if (([riscv_instr_category_t.ARITHMETIC].canFind(category)) &&
	  (group == riscv_instr_group_t.RV32B)) {
	binary = format("%8h", toubvec!6(0b00_0010) ~ cast(ubvec!6) (imm[0..6]) ~
			toubvec!5(rs1) ~ get_func3() ~ toubvec!5(rd) ~ get_opcode());
      }

      if (([riscv_instr_category_t.ARITHMETIC].canFind(category)) &&
	  (group == riscv_instr_group_t.RV64B)) {
	binary = format("%8h", cast(ubvec!12) imm[0..12] ~ toubvec!5(rs1) ~ get_func3() ~
			toubvec!5(rd) ~ get_opcode());
      }
      break;

    case riscv_instr_format_t.R4_FORMAT:
      binary = format("%8h", toubvec!5(rs3) ~ get_func2() ~ toubvec!5(rs2) ~ toubvec!5(rs1) ~
		      get_func3() ~ toubvec!5(rd) ~ get_opcode());
      break;
    default:
      if (binary == "") binary = super.convert2bin(prefix);
    }

    return prefix ~ binary;
  }

  override void do_copy(uvm_object rhs) {
    super.copy(rhs);
    riscv_b_instr rhs_ = cast(riscv_b_instr) rhs;
    assert (rhs_ !is null);
    this.rs3 = rhs_.rs3;
    this.has_rs3 = rhs_.has_rs3;
  }

  override bool is_supported(riscv_instr_gen_config cfg) {
    return cfg.enable_b_extension &&
      (((canFind(cfg.enable_bitmanip_groups, b_ext_group_t.ZBP)) &&
	[riscv_instr_name_t.GREV, riscv_instr_name_t.GREVW,
	 riscv_instr_name_t.GREVI, riscv_instr_name_t.GREVIW,
	 riscv_instr_name_t.GORC, riscv_instr_name_t.GORCW,
	 riscv_instr_name_t.GORCI, riscv_instr_name_t.GORCIW,
	 riscv_instr_name_t.SHFL, riscv_instr_name_t.SHFLW,
	 riscv_instr_name_t.UNSHFL, riscv_instr_name_t.UNSHFLW,
	 riscv_instr_name_t.SHFLI, riscv_instr_name_t.UNSHFLI,
	 riscv_instr_name_t.XPERM_N, riscv_instr_name_t.XPERM_B,
	 riscv_instr_name_t.XPERM_H, riscv_instr_name_t.XPERM_W,
	 riscv_instr_name_t.SLO, riscv_instr_name_t.SLOW,
	 riscv_instr_name_t.SLOI, riscv_instr_name_t.SLOIW,
	 riscv_instr_name_t.SRO, riscv_instr_name_t.SROW,
	 riscv_instr_name_t.SROI, riscv_instr_name_t.SROIW].canFind(instr_name)) ||
       ((canFind(cfg.enable_bitmanip_groups, b_ext_group_t.ZBE)) &&
	[riscv_instr_name_t.BCOMPRESS, riscv_instr_name_t.BDECOMPRESS,
	 riscv_instr_name_t.BCOMPRESSW, riscv_instr_name_t.BDECOMPRESSW].canFind(instr_name)) ||
       ((canFind(cfg.enable_bitmanip_groups, b_ext_group_t.ZBF)) &&
	[riscv_instr_name_t.BFP, riscv_instr_name_t.BFPW].canFind(instr_name)) ||
       ((canFind(cfg.enable_bitmanip_groups, b_ext_group_t.ZBR)) &&
	[riscv_instr_name_t.CRC32_B, riscv_instr_name_t.CRC32_H,
	 riscv_instr_name_t.CRC32_W, riscv_instr_name_t.CRC32_D,
	 riscv_instr_name_t.CRC32C_B, riscv_instr_name_t.CRC32C_H,
	 riscv_instr_name_t.CRC32C_W, riscv_instr_name_t.CRC32C_D].canFind(instr_name)) ||
       ((canFind(cfg.enable_bitmanip_groups, b_ext_group_t.ZBM)) &&
	[riscv_instr_name_t.BMATOR, riscv_instr_name_t.BMATXOR,
	 riscv_instr_name_t.BMATFLIP].canFind(instr_name)) ||
       ((canFind(cfg.enable_bitmanip_groups, b_ext_group_t.ZBT)) &&
	[riscv_instr_name_t.CMOV, riscv_instr_name_t.CMIX,
	 riscv_instr_name_t.FSL, riscv_instr_name_t.FSLW,
	 riscv_instr_name_t.FSR, riscv_instr_name_t.FSRW,
	 riscv_instr_name_t.FSRI, riscv_instr_name_t.FSRIW].canFind(instr_name)));
  }

  // // coverage related functons
  // void update_src_regs(string[] operands) {
  //   // handle special I_FORMAT (FSRI, FSRIW) and R4_FORMAT
  //   switch(instr_format) {
  //   case riscv_instr_format_t.I_FORMAT:
  //     if ([riscv_instr_name_t.FSRI, riscv_instr_name_t.FSRIW].canFind(instr_name)) {
  // 	assert (operands.length == 4);
  // 	// fsri rd, rs1, rs3, imm
  // 	rs1 = get_gpr(operands[1]);
  // 	rs1_value = get_gpr_state(operands[1]);
  // 	rs3 = get_gpr(operands[2]);
  // 	rs3_value = get_gpr_state(operands[2]);
  // 	get_val(operands[3], imm);
  // 	return;
  //     }
  //     break;
  //   case riscv_instr_format_t.R4_FORMAT:
  //     assert (operands.length == 4);
  //     rs1 = get_gpr(operands[1]);
  //     rs1_value = get_gpr_state(operands[1]);
  //     rs2 = get_gpr(operands[2]);
  //     rs2_value = get_gpr_state(operands[2]);
  //     rs3 = get_gpr(operands[3]);
  //     rs3_value = get_gpr_state(operands[3]);
  //     return;
  //   default: break;
  //   }
  //   // reuse base function to handle the other instructions
  //   super.update_src_regs(operands);
  // }
}
