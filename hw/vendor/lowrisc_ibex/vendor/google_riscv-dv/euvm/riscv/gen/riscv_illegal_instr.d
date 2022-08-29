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

// ---------------------------------------------------------------------------------------------
// This class is used to generate illegal or HINT instructions.
// The illegal instruction will be generated in binary format and mixed with other valid instr.
// The mixed instruction stream will be stored in data section and loaded to instruction pages
// at run time.
// ---------------------------------------------------------------------------------------------

module riscv.gen.riscv_illegal_instr;

import riscv.gen.riscv_instr_pkg: privileged_reg_t, riscv_instr_group_t;
import riscv.gen.target: supported_isa, XLEN, custom_csr;
import riscv.gen.riscv_instr_gen_config: riscv_instr_gen_config;
import std.traits: EnumMembers;
import std.format: format;
import std.algorithm: canFind;

import esdl.data.bvec: ubvec, toubvec;
import esdl.rand: rand, constraint;

import uvm;

class riscv_illegal_instr: uvm_object
{
  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  string comment;

  enum illegal_instr_type_e: ubyte {
    kIllegalOpcode,
    kIllegalCompressedOpcode,
    kIllegalFunc3,
    kIllegalFunc7,
    kReservedCompressedInstr,
    kHintInstr,
    kIllegalSystemInstr
  }

  enum reserved_c_instr_e: ubyte {
    kIllegalCompressed,
    kReservedAddispn,
    kReservedAddiw,
    kReservedAddi16sp,
    kReservedLui,
    kReservedLwsp,
    kReservedLdsp,
    kReservedLqsp,
    kReservedJr,
    kReservedC0,
    kReservedC1,
    kReservedC2
  }

  // Default legal opcode for RV32I instructions
  ubvec!7[]  legal_opcode = [0b0000011.toubvec!7,
			     0b0001111.toubvec!7,
			     0b0010011.toubvec!7,
			     0b0010111.toubvec!7,
			     0b0100011.toubvec!7,
			     0b0110111.toubvec!7,
			     0b1100011.toubvec!7,
			     0b0110011.toubvec!7,
			     0b1100111.toubvec!7,
			     0b1110011.toubvec!7,
			     0b1101111.toubvec!7];

  // Default legal opcode for RV32C instructions
  ubvec!3[] legal_c00_opcode = [0b000.toubvec!3,
				0b010.toubvec!3,
				0b110.toubvec!3];
  ubvec!3[] legal_c10_opcode = [0b000.toubvec!3,
				0b010.toubvec!3,
				0b100.toubvec!3,
				0b110.toubvec!3];

  @rand illegal_instr_type_e  exception;
  @rand reserved_c_instr_e    reserved_c;
  @rand ubvec!32              instr_bin;
  @rand ubvec!7               opcode;
  @rand bool                  compressed;
  @rand ubvec!3               func3;
  @rand ubvec!7               func7;
  @rand bool                  has_func3;
  @rand bool                  has_func7;
  @rand ubvec!2               c_op;
  @rand ubvec!3               c_msb;
  riscv_instr_gen_config      cfg;
  privileged_reg_t[]          csrs;

  constraint!  q{
    exception dist [
		    illegal_instr_type_e.kIllegalOpcode           := 3,
		    illegal_instr_type_e.kIllegalCompressedOpcode := 1,
		    illegal_instr_type_e.kIllegalFunc3            := 1,
		    illegal_instr_type_e.kIllegalFunc7            := 1,
		    illegal_instr_type_e.kReservedCompressedInstr := 1,
		    illegal_instr_type_e.kHintInstr               := 3,
		    illegal_instr_type_e.kIllegalSystemInstr      := 3
		    ];
    if (riscv_instr_group_t.RV32C !inside [supported_isa]) {
      exception != illegal_instr_type_e.kHintInstr;
      compressed == false;
    }
  } exception_dist_c;

  constraint!  q{
    solve opcode before instr_bin;
    solve func3 before instr_bin;
    solve func7 before instr_bin;
    solve c_msb before instr_bin;
    solve c_op before instr_bin;
    if (compressed == true) {
      instr_bin[0..2] == c_op;
      instr_bin[13..16] == c_msb;
    }
    else {
      instr_bin[0..7] == opcode;
      if (has_func7 == true) {
        instr_bin[25..32] == func7;
      }
      if (has_func3 == true) {
        instr_bin[12..15] == func3;
      }
    }
  } instr_bit_assignment_c;

  // Invalid SYSTEM instructions
  constraint!  q{
    if (exception == illegal_instr_type_e.kIllegalSystemInstr) {
      opcode == 0b1110011;
      // ECALL/EBREAK/xRET/WFI
      if (func3 == 0b000) {
        // Constrain RS1 and RD to be non-zero
        instr_bin[15..20] != 0;
        instr_bin[7..12] != 0;
        // Valid SYSTEM instructions considered by this
        // Constrain the upper 12 bits to be invalid
        instr_bin[20..32] !inside [0x0, 0x1, 0x2, 0x102, 0x302, 0x7b2, 0x105];
      }
      else {
        // Invalid CSR instructions
        instr_bin[20..32] !inside [csrs];
        instr_bin[20..32] !inside [custom_csr];
      }
    }
  } system_instr_c;

  constraint!  q{
    if ((c_msb == 0b000) && (c_op == 0b10) && (XLEN == 32)) {
      if (exception == illegal_instr_type_e.kReservedCompressedInstr) {
        instr_bin[12] == 1;
      }
      else {
        instr_bin[12] == 0;
      }
    }
  } legal_rv32_c_slli;

  constraint!  q{
    if (compressed == true ) {
      exception inside [illegal_instr_type_e.kReservedCompressedInstr,
			illegal_instr_type_e.kIllegalCompressedOpcode,
			illegal_instr_type_e.kHintInstr];
    }
    else {
      exception inside [illegal_instr_type_e.kIllegalOpcode,
			illegal_instr_type_e.kIllegalFunc3,
			illegal_instr_type_e.kIllegalFunc7,
			illegal_instr_type_e.kIllegalSystemInstr];
    }
    if (!has_func7) {
      exception != illegal_instr_type_e.kIllegalFunc7;
    }
    if (!has_func3) {
      exception != illegal_instr_type_e.kIllegalFunc3;
    }
  } exception_type_c;

  constraint!  q{
    c_op != 0b11;
  } compressed_instr_op_c;

  // Avoid generating illegal func3/func7 errors for opcode used by B-extension for now
  //
  // TODO(udi): add support for generating illegal B-extension instructions
  constraint!  q{
    if (riscv_instr_group_t.RV32B inside [supported_isa]) {
      if (exception inside [illegal_instr_type_e.kIllegalFunc3,
			    illegal_instr_type_e.kIllegalFunc7]) {
        opcode !inside [0b0110011, 0b0010011, 0b0111011];
      }
    }
  } b_extension_c;

  constraint!  q{
    if (riscv_instr_group_t.RV32ZBA inside [supported_isa]) {
      if (exception inside [illegal_instr_type_e.kIllegalFunc3,
			    illegal_instr_type_e.kIllegalFunc7]) {
        opcode !inside [0b0110011, 0b0111011, 0b0011011];
      }
    }
  } zba_extension_c;

  constraint! q{
    if (riscv_instr_group_t.RV32ZBB inside [supported_isa]) {
      if (exception inside [illegal_instr_type_e.kIllegalFunc3,
			    illegal_instr_type_e.kIllegalFunc7]) {
        opcode !inside [0b0110011, 0b0010011, 0b0111011, 0b0011011];
      }
    }
  } zbb_extension_c;

  constraint! q{
    if (riscv_instr_group_t.RV32ZBB inside [supported_isa]) {
      if (exception inside [illegal_instr_type_e.kIllegalFunc3,
			    illegal_instr_type_e.kIllegalFunc7]) {
        opcode !inside [0b0110011];
      }
    }
  } zbc_extension_c;

  constraint! q{
    if (riscv_instr_group_t.RV32ZBS inside [supported_isa]) {
      if (exception inside [illegal_instr_type_e.kIllegalFunc3,
			    illegal_instr_type_e.kIllegalFunc7]) {
        opcode !inside [0b0110011, 0b0010011];
      }
    }
  } zbs_extension_c;

  constraint!  q{
    if (exception == illegal_instr_type_e.kIllegalCompressedOpcode) {
      c_op != 0b01;
      if (legal_c00_opcode.length == 8) {
        c_op != 0b00;
      }
      else {
        c_msb !inside [legal_c00_opcode];
      }
      if (legal_c10_opcode.length == 8) {
        c_op != 0b10;
      }
      else {
        c_msb !inside [legal_c10_opcode];
      }
    }
  } illegal_compressed_op_c;

  constraint!  q{
    solve exception  before reserved_c;
    solve exception  before opcode;
    solve reserved_c before instr_bin;
    solve reserved_c before c_msb;
    solve reserved_c before c_op;
    if (XLEN == 32) {
      //c.addiw is RV64/RV128 only instruction, the encoding is used for C.JAL for RV32C
      reserved_c != reserved_c_instr_e.kReservedAddiw;
    }
    if (exception == illegal_instr_type_e.kReservedCompressedInstr) {
      (reserved_c == reserved_c_instr_e.kIllegalCompressed) ->
	(instr_bin[0..16] == 0);
      (reserved_c == reserved_c_instr_e.kReservedAddispn) ->
	((instr_bin[5..16] == 0) && (c_op == 0b00));
      (reserved_c == reserved_c_instr_e.kReservedAddiw) ->
	(c_msb == 0b001 && c_op == 0b01 && instr_bin[7..12] == 0b0);
      (reserved_c == reserved_c_instr_e.kReservedC0) ->
	(instr_bin[10..16] == 0b100111 && instr_bin[5..7] == 0b10 && c_op == 0b01);
      (reserved_c == reserved_c_instr_e.kReservedC1) ->
	(instr_bin[10..16] == 0b100111 && instr_bin[5..7] == 0b11 && c_op == 0b01);
      (reserved_c == reserved_c_instr_e.kReservedC2) ->
	(c_msb == 0b100 && c_op == 0b00);
      (reserved_c == reserved_c_instr_e.kReservedAddi16sp) ->
	(c_msb == 0b011 && c_op == 0b01 && instr_bin[7..12] == 2 &&
	 instr_bin[12] == 0 && instr_bin[2..7] == 0);
      (reserved_c == reserved_c_instr_e.kReservedLui) ->
	(c_msb == 0b011 && c_op == 0b01 && instr_bin[12] == 0 && instr_bin[2..7] ==0);
      (reserved_c == reserved_c_instr_e.kReservedJr) ->
	(instr_bin == 0b1000_0000_0000_0010);
      (reserved_c == reserved_c_instr_e.kReservedLqsp) ->
	(c_msb == 0b001 && c_op == 0b10 && instr_bin[7..12] == 0);
      (reserved_c == reserved_c_instr_e.kReservedLwsp) ->
	(c_msb == 0b010 && c_op == 0b10 && instr_bin[7..12] == 0);
      (reserved_c == reserved_c_instr_e.kReservedLdsp) ->
	(c_msb == 0b011 && c_op == 0b10 && instr_bin[7..12] == 0b0);
    }
  } reserved_compressed_instr_c;

  constraint!  q{
    if (exception == illegal_instr_type_e.kHintInstr) {
      // C.ADDI
      (c_msb == 0b000 && c_op == 0b01 && instr_bin[12] == 0 && instr_bin[2..7] == 0b00000) ||
	// C.LI
	(c_msb == 0b010 && c_op == 0b01 && instr_bin[7..12] == 0b0) ||
	// C.SRAI64, C.SRLI64
	(c_msb == 0b100 && c_op == 0b01 && instr_bin[11..13] == 0b00 &&
	 instr_bin[2..7] == 0b00000) ||
	// C.MV
	(c_msb == 0b100 && c_op == 0b10 && instr_bin[7..12] == 0b00000 &&
	 instr_bin[2..7]  != 0b00000) ||
	// C.LUI
	(c_msb == 0b011 && c_op == 0b01 && instr_bin[7..12] == 0b00000 &&
	 (instr_bin[12] != 0 || instr_bin[2..7] != 0b00000)) ||
	// C.SLLI
	(c_msb == 0b000 && c_op == 0b10 && instr_bin[7..12] == 0b00000)  ||
	// C.SLLI64
	(c_msb == 0b000 && c_op == 0b10 && instr_bin[7..12] != 0b00000 && instr_bin[12] == 0b0 &&
	 instr_bin[2..7] == 0b00000)  ||
	// C.ADD
	(c_msb == 0b100 && c_op == 0b10 && instr_bin[7..12] == 0b00000 && instr_bin[12] == 0b1 &&
	 instr_bin[2..7] != 0b00000);
    }
  } hint_instr_c;

  constraint!  q{
    solve opcode before instr_bin;
    if (exception == illegal_instr_type_e.kIllegalOpcode) {
      !(opcode inside [legal_opcode]);
      opcode[0..2] == 0b11;
    }
    else {
      opcode inside [legal_opcode];
    }
  } illegal_opcode_c;

  // TODO: Enable atomic instruction
  constraint!  q{
    if (exception != illegal_instr_type_e.kIllegalOpcode) {
      opcode != 0b0101111;
    }
  } no_atomic_c;

  constraint!  q{
    solve opcode before func3;
    if (compressed == false) {
      if (exception == illegal_instr_type_e.kIllegalFunc3) {
	(opcode == 0b1100111) -> (func3 != 0b000);
	(opcode == 0b1100011) -> (func3 inside [0b010, 0b011]);

        if (XLEN == 32) {
	  (opcode == 0b0100011) -> (func3 >= 0b011);
	  (opcode == 0b0000011) -> (func3 inside [0b011, 0b111]);
        } else {
	  (opcode == 0b0100011) -> (func3 > 0b011);
	  (opcode == 0b0000011) -> (func3 == 0b111);
        }
	(opcode == 0b0001111) -> (func3 !inside [0b000, 0b001]);
	(opcode == 0b1110011) -> (func3 == 0b100);
	(opcode == 0b0011011) -> (func3 !inside [0b000, 0b001, 0b101]);
	(opcode == 0b0111011) -> (func3 inside [0b010, 0b011]);
        opcode inside [0b1100111, 0b1100011, 0b0000011, 0b0100011,
                       0b0001111, 0b1110011, 0b0011011, 0b0111011];
      }
      else {
	(opcode == 0b1100111) -> (func3 == 0b000);
	(opcode == 0b1100011) -> (func3 !inside [0b010, 0b011]);
        if (XLEN == 32) {
	  (opcode == 0b0100011) -> (func3 < 0b011);
	  (opcode == 0b0000011) -> (func3 !inside [0b011, 0b111]);
        }
	else {
	  (opcode == 0b0100011) -> (func3 <= 0b011);
	  (opcode == 0b0000011) -> (func3 != 0b111);
        }
	(opcode == 0b0001111) -> (func3 inside [0b000, 0b001]);
	(opcode == 0b1110011) -> (func3 != 0b100);
	(opcode == 0b0011011) -> (func3 inside [0b000, 0b001, 0b101]);
	(opcode == 0b0111011) -> (func3 !inside [0b010, 0b011]);
      }
    }

  } illegal_func3_c;

  constraint! q{
    solve opcode before func7;
    if ((opcode == 0b0010011) && (func3 ==  0b001) || (func3 == 0b101) ||
	(opcode == 0b0110011) || (opcode == 0b0111011)) {
      has_func7 == true;
    }
    else {
      has_func7 == false;
    }
  } has_func7_c;

  constraint!  q{
    solve opcode before func7;
    if (opcode inside [0b0110111, 0b1101111, 0b0010111]) {
      has_func3 == false;
    }
    else {
      has_func3 == true;
    }
  } has_func3_c;

  constraint!  q{
    if (compressed == false) {
      if (exception == illegal_instr_type_e.kIllegalFunc7) {
	!(func7 inside [0, 0b0100000, 1]);
        if (opcode == 0b0001001) { // SLLI, SRLI, SRAI
          !(func7[6:1] inside [0, 0b010000]);
        }
      } else {
        func7 inside [0, 0b0100000, 1];
      }
    }
  } illegal_func7_c;


  // `uvm_object_utils(riscv_illegal_instr)
  // `uvm_object_new

  void init(riscv_instr_gen_config cfg) {
    privileged_reg_t csr;
    this.cfg = cfg;
    if ((canFind(supported_isa, riscv_instr_group_t.RV32F) ||
	 canFind(supported_isa, riscv_instr_group_t.RV32D))) {
      legal_opcode ~= [0b0000111.toubvec!7, 0b0100111.toubvec!7, 0b1000011.toubvec!7,
		       0b1000111.toubvec!7, 0b1001011.toubvec!7, 0b1001111.toubvec!7,
		       0b1010011.toubvec!7] ;
    }
    if (canFind(supported_isa, riscv_instr_group_t.RV64I)) {
      legal_opcode ~= [0b0011011.toubvec!7];
    }
    if (canFind(supported_isa, riscv_instr_group_t.RV32A)) {
      legal_opcode ~= [0b0101111.toubvec!7];
    }
    if (canFind(supported_isa, riscv_instr_group_t.RV64I)  ||
	canFind(supported_isa,  riscv_instr_group_t.RV64M )) {
      legal_opcode ~= [0b0111011.toubvec!7];
    }
    if (canFind(supported_isa, riscv_instr_group_t.RV64I)) {
      legal_c00_opcode ~= [0b011.toubvec!3, 0b111.toubvec!3];
      legal_c10_opcode ~= [0b011.toubvec!3, 0b111.toubvec!3];
    }
    // csr = csr.first();
    // for (int i = 0; i < csr.num(); i = i + 1) begin
    //   csrs.push_back(csr);
    //   csr = csr.next();
    // end

    csrs = [EnumMembers!privileged_reg_t];
  }

  string get_bin_str() {
    import std.conv: to;
    string str;
    if (compressed) {
      str = format("%4h", (cast(ubvec!16) instr_bin[0..16]));
    }
    else {
      str =  format("%8h", (cast(ubvec!32) instr_bin[0..31]));
    }
    uvm_info(get_full_name(), format("Illegal instruction type: %0s, illegal instruction: 0x%0x",
				     exception, instr_bin), UVM_HIGH);
    return str;
  }

  void post_randomize() {
    import std.conv: to;
    comment = to!string(exception);
    if (exception == illegal_instr_type_e.kReservedCompressedInstr) {
      comment ~= " " ~ to!string(reserved_c);
    }
    else if (exception == illegal_instr_type_e.kIllegalOpcode) {
      comment ~= " " ~ format("%7b", opcode);
    }
  }

}
