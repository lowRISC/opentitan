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

module riscv.gen.isa.riscv_instr;

import riscv.gen.riscv_instr_pkg: riscv_instr_group_t, riscv_instr_format_t,
  riscv_instr_category_t, riscv_instr_name_t, imm_t, riscv_reg_t, format_string,
  MAX_INSTR_STR_LEN;
import riscv.gen.target: XLEN;
import riscv.gen.riscv_instr_gen_config: riscv_instr_gen_config;
// import riscv.gen.riscv_instr_registry: riscv_instr_registry;

import esdl.data.bvec: bvec, ubvec, toubvec;
import esdl.rand: rand, constraint;

import std.format: format;
import std.algorithm.searching: canFind;

import uvm;

class riscv_instr: uvm_object
{
  mixin uvm_object_utils;

  riscv_instr_gen_config     m_cfg;
  // riscv_instr_registry       m_registry;

  // Instruction attributes
  riscv_instr_group_t        group;
  riscv_instr_format_t       instr_format;
  riscv_instr_category_t     category;
  riscv_instr_name_t         instr_name;
  imm_t                      imm_type;
  ubvec!5                    imm_len;

  // Operands
  @rand ubvec!12             csr;
  @rand riscv_reg_t          rs2;
  @rand riscv_reg_t          rs1;
  @rand riscv_reg_t          rd;
  @rand ubvec!32             imm;

  // Helper fields
  ubvec!32                   imm_mask = 0xFFFF_FFFF;
  bool                       is_branch_target;
  bool                       has_label = true;
  bool                       atomic = false;
  bool                       branch_assigned;
  bool                       process_load_store = true;
  bool                       is_compressed;
  bool                       is_illegal_instr;
  bool                       is_hint_instr;
  bool                       is_floating_point;
  string                     imm_str;
  string                     comment;
  string                     label;
  bool                       is_local_numeric_label;
  int                        idx = -1;
  bool                       has_rs1 = true;
  bool                       has_rs2 = true;
  bool                       has_rd = true;
  bool                       has_imm = true;


  constraint! q{
    if (instr_name inside [riscv_instr_name_t.SLLIW,
			   riscv_instr_name_t.SRLIW,
			   riscv_instr_name_t.SRAIW]) {
      imm[5..12] == 0;
    }
    if (instr_name inside [riscv_instr_name_t.SLLI,
			   riscv_instr_name_t.SRLI,
			   riscv_instr_name_t.SRAI]) {
      if (XLEN == 32) {
        imm[5..12] == 0;
      }
      else {
        imm[6..12] == 0;
      }
    }
  } imm_c;

  constraint!  q{
    if (category == riscv_instr_category_t.CSR) {
      if (m_cfg.instr_registry.include_reg.length > 0) {
        csr inside [m_cfg.instr_registry.include_reg];
      }
      if (m_cfg.instr_registry.exclude_reg.length > 0) {
        csr !inside [m_cfg.instr_registry.exclude_reg];
      }
    }
  } csr_c;

  this(string name = "") {
    super(name);
  }

  bool is_supported(riscv_instr_gen_config cfg) {
    return true;
  }


  // // Disable the rand mode for unused operands to randomization performance
  void set_rand_mode() {
    switch (instr_format) {
    case riscv_instr_format_t.R_FORMAT:
      has_imm = false;
      break;
    case riscv_instr_format_t.I_FORMAT:
      has_rs2 = false;
      break;
    case riscv_instr_format_t.S_FORMAT, riscv_instr_format_t.B_FORMAT:
      has_rd = false;
      break;
    case riscv_instr_format_t.U_FORMAT, riscv_instr_format_t.J_FORMAT:
      has_rs1 = false;
      has_rs2 = false;
      break;
    default: break;
    }
    if (category == riscv_instr_category_t.CSR) {
      has_rs2 = false;
      if (instr_format ==riscv_instr_format_t.I_FORMAT) {
	has_rs1 = false;
      }
    }
  }

  void pre_randomize() {
    rand_mode!q{rs1}(has_rs1);
    rand_mode!q{rs2}(has_rs2);
    rand_mode!q{rd}(has_rd);
    rand_mode!q{imm}(has_imm);
    if (category != riscv_instr_category_t.CSR) {
      rand_mode!q{csr}(0);
    }
  }

  void set_imm_len() {
    if (instr_format == riscv_instr_format_t.U_FORMAT ||
	instr_format == riscv_instr_format_t.J_FORMAT) {
      imm_len = toubvec!5(20);
    }
    else if (instr_format == riscv_instr_format_t.I_FORMAT ||
	     instr_format == riscv_instr_format_t.S_FORMAT ||
	     instr_format == riscv_instr_format_t.B_FORMAT) {
      if (imm_type == imm_t.UIMM) {
	imm_len = toubvec!5(5);
      }
      else {
	imm_len = toubvec!5(11);
      }
    }
    imm_mask = imm_mask << imm_len;
  }

  void extend_imm() {
    bool sign;
    imm = imm << (32 - imm_len);
    sign = imm[31];
    imm = imm >> (32 - imm_len);
    // Signed extension
    if (sign &&	!(instr_format == riscv_instr_format_t.U_FORMAT ||
		  imm_type == imm_t.UIMM ||
		  imm_type == imm_t.NZUIMM)) {
      imm = imm_mask | imm;
    }
  }

  void post_randomize() {
    extend_imm();
    update_imm_str();
  }

  // Convert the instruction to assembly code
  string convert2asm(string prefix = "") {
    import std.string: toLower;
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    if (category != riscv_instr_category_t.SYSTEM) {
      switch (instr_format) {
      case riscv_instr_format_t.J_FORMAT, riscv_instr_format_t.U_FORMAT: // instr rd,imm
	asm_str = format("%0s%0s, %0s", asm_str, rd, get_imm());
	break;
      case riscv_instr_format_t.I_FORMAT: // instr rd,rs1,imm
	if (instr_name == riscv_instr_name_t.NOP)
	  asm_str = "nop";
	else if (instr_name == riscv_instr_name_t.WFI)
	  asm_str = "wfi";
	else if (instr_name == riscv_instr_name_t.FENCE)
	  asm_str = format("fence"); // TODO: Support all fence combinations
	else if (instr_name == riscv_instr_name_t.FENCE_I)
	  asm_str = "fence.i";
	else if (category == riscv_instr_category_t.LOAD) // Use psuedo instruction format
	  asm_str = format("%0s%0s, %0s(%0s)", asm_str, rd, get_imm(), rs1);
	else if (category == riscv_instr_category_t.CSR)
	  asm_str = format("%0s%0s, 0x%0x, %0s", asm_str,rd, csr, get_imm());
	else
	  asm_str = format("%0s%0s, %0s, %0s", asm_str, rd, rs1, get_imm());
	break;
      case riscv_instr_format_t.S_FORMAT, riscv_instr_format_t.B_FORMAT: // instr rs1,rs2,imm
	if (category == riscv_instr_category_t.STORE) // Use psuedo instruction format
	  asm_str = format("%0s%0s, %0s(%0s)", asm_str, rs2, get_imm(), rs1);
	else
	  asm_str = format("%0s%0s, %0s, %0s", asm_str, rs1, rs2, get_imm());
	break;
      case riscv_instr_format_t.R_FORMAT: // instr rd,rs1,rs2
	if (category ==  riscv_instr_category_t.CSR) {
	  asm_str = format("%0s%0s, 0x%0x, %0s", asm_str, rd, csr, rs1);
	}
	else if (instr_name == riscv_instr_name_t.SFENCE_VMA) {
	  asm_str = "sfence.vma x0, x0"; // TODO: Support all possible sfence
	}
	else {
	  asm_str = format("%0s%0s, %0s, %0s", asm_str, rd, rs1, rs2);
	}
	break;
      default: uvm_fatal(get_full_name(), format("Unsupported format %0s [%0s]",
						   instr_format, instr_name));
	break;
      }
    }
    else {
      // For EBREAK,C.EBREAK, making sure pc+4 is a valid instruction boundary
      // This is needed to resume execution from epc+4 after ebreak handling
      if (instr_name == riscv_instr_name_t.EBREAK) {
	asm_str = ".4byte 0x00100073 # ebreak";
      }
    }
    if (comment != "")
      asm_str = asm_str ~ " #" ~comment;
    return toLower(asm_str);
  }

  ubvec!7 get_opcode() {
    switch (instr_name) {
    case riscv_instr_name_t.LUI:       return toubvec!7(0b0110111);
    case riscv_instr_name_t.AUIPC:     return toubvec!7(0b0010111);
    case riscv_instr_name_t.JAL:       return toubvec!7(0b1101111);
    case riscv_instr_name_t.JALR:      return toubvec!7(0b1100111);
    case riscv_instr_name_t.BEQ,
      riscv_instr_name_t.BNE,
      riscv_instr_name_t.BLT,
      riscv_instr_name_t.BGE,
      riscv_instr_name_t.BLTU,
      riscv_instr_name_t.BGEU:         return toubvec!7(0b1100011);
    case riscv_instr_name_t.LB,
      riscv_instr_name_t.LH,
      riscv_instr_name_t.LW,
      riscv_instr_name_t.LBU,
      riscv_instr_name_t.LHU,
      riscv_instr_name_t.LWU,
      riscv_instr_name_t.LD:           return toubvec!7(0b0000011);
    case riscv_instr_name_t.SB,
      riscv_instr_name_t.SH,
      riscv_instr_name_t.SW,
      riscv_instr_name_t.SD:           return toubvec!7(0b0100011);
    case riscv_instr_name_t.ADDI,
      riscv_instr_name_t.SLTI,
      riscv_instr_name_t.SLTIU,
      riscv_instr_name_t.XORI,
      riscv_instr_name_t.ORI,
      riscv_instr_name_t.ANDI,
      riscv_instr_name_t.SLLI,
      riscv_instr_name_t.SRLI,
      riscv_instr_name_t.SRAI,
      riscv_instr_name_t.NOP:          return toubvec!7(0b0010011);
    case riscv_instr_name_t.ADD,
      riscv_instr_name_t.SUB,
      riscv_instr_name_t.SLL,
      riscv_instr_name_t.SLT,
      riscv_instr_name_t.SLTU,
      riscv_instr_name_t.XOR,
      riscv_instr_name_t.SRL,
      riscv_instr_name_t.SRA,
      riscv_instr_name_t.OR,
      riscv_instr_name_t.AND,
      riscv_instr_name_t.MUL,
      riscv_instr_name_t.MULH,
      riscv_instr_name_t.MULHSU,
      riscv_instr_name_t.MULHU,
      riscv_instr_name_t.DIV,
      riscv_instr_name_t.DIVU,
      riscv_instr_name_t.REM,
      riscv_instr_name_t.REMU:         return toubvec!7(0b0110011);
    case riscv_instr_name_t.ADDIW,
      riscv_instr_name_t.SLLIW,
      riscv_instr_name_t.SRLIW,
      riscv_instr_name_t.SRAIW:        return toubvec!7(0b0011011);
    // case riscv_instr_name_t.MULH,
    //   riscv_instr_name_t.MULHSU,
    //   riscv_instr_name_t.MULHU,
    //   riscv_instr_name_t.DIV,
    //   riscv_instr_name_t.DIVU,
    //   riscv_instr_name_t.REM,
    //   riscv_instr_name_t.REMU: { return toubvec!0b0110011;
    case riscv_instr_name_t.FENCE,
      riscv_instr_name_t.FENCE_I:      return toubvec!7(0b0001111);
    case riscv_instr_name_t.CSRRW,
      riscv_instr_name_t.CSRRS,
      riscv_instr_name_t.CSRRC,
      riscv_instr_name_t.CSRRWI,
      riscv_instr_name_t.CSRRSI,
      riscv_instr_name_t.CSRRCI:       return toubvec!7(0b1110011);
    case riscv_instr_name_t.ADDW,
      riscv_instr_name_t.SUBW,
      riscv_instr_name_t.SLLW,
      riscv_instr_name_t.SRLW,
      riscv_instr_name_t.SRAW,
      riscv_instr_name_t.MULW,
      riscv_instr_name_t.DIVW,
      riscv_instr_name_t.DIVUW,
      riscv_instr_name_t.REMW,
      riscv_instr_name_t.REMUW:        return toubvec!7(0b0111011);
    case riscv_instr_name_t.ECALL,
      riscv_instr_name_t.EBREAK,
      riscv_instr_name_t.URET,
      riscv_instr_name_t.SRET,
      riscv_instr_name_t.MRET,
      riscv_instr_name_t.DRET,
      riscv_instr_name_t.WFI,
      riscv_instr_name_t.SFENCE_VMA:   return toubvec!7(0b1110011);
    default: uvm_fatal(get_full_name(), format("Unsupported instruction %0s", instr_name));
      assert (false);
    }
  }

  ubvec!3 get_func3() {
    switch (instr_name) {
    case riscv_instr_name_t.JALR:       return toubvec!3(0b000);
    case riscv_instr_name_t.BEQ:        return toubvec!3(0b000);
    case riscv_instr_name_t.BNE:        return toubvec!3(0b001);
    case riscv_instr_name_t.BLT:        return toubvec!3(0b100);
    case riscv_instr_name_t.BGE:        return toubvec!3(0b101);
    case riscv_instr_name_t.BLTU:       return toubvec!3(0b110);
    case riscv_instr_name_t.BGEU:       return toubvec!3(0b111);
    case riscv_instr_name_t.LB:         return toubvec!3(0b000);
    case riscv_instr_name_t.LH:         return toubvec!3(0b001);
    case riscv_instr_name_t.LW:         return toubvec!3(0b010);
    case riscv_instr_name_t.LBU:        return toubvec!3(0b100);
    case riscv_instr_name_t.LHU:        return toubvec!3(0b101);
    case riscv_instr_name_t.SB:         return toubvec!3(0b000);
    case riscv_instr_name_t.SH:         return toubvec!3(0b001);
    case riscv_instr_name_t.SW:         return toubvec!3(0b010);
    case riscv_instr_name_t.ADDI:       return toubvec!3(0b000);
    case riscv_instr_name_t.NOP:        return toubvec!3(0b000);
    case riscv_instr_name_t.SLTI:       return toubvec!3(0b010);
    case riscv_instr_name_t.SLTIU:      return toubvec!3(0b011);
    case riscv_instr_name_t.XORI:       return toubvec!3(0b100);
    case riscv_instr_name_t.ORI:        return toubvec!3(0b110);
    case riscv_instr_name_t.ANDI:       return toubvec!3(0b111);
    case riscv_instr_name_t.SLLI:       return toubvec!3(0b001);
    case riscv_instr_name_t.SRLI:       return toubvec!3(0b101);
    case riscv_instr_name_t.SRAI:       return toubvec!3(0b101);
    case riscv_instr_name_t.ADD:        return toubvec!3(0b000);
    case riscv_instr_name_t.SUB:        return toubvec!3(0b000);
    case riscv_instr_name_t.SLL:        return toubvec!3(0b001);
    case riscv_instr_name_t.SLT:        return toubvec!3(0b010);
    case riscv_instr_name_t.SLTU:       return toubvec!3(0b011);
    case riscv_instr_name_t.XOR:        return toubvec!3(0b100);
    case riscv_instr_name_t.SRL:        return toubvec!3(0b101);
    case riscv_instr_name_t.SRA:        return toubvec!3(0b101);
    case riscv_instr_name_t.OR:         return toubvec!3(0b110);
    case riscv_instr_name_t.AND:        return toubvec!3(0b111);
    case riscv_instr_name_t.FENCE:      return toubvec!3(0b000);
    case riscv_instr_name_t.FENCE_I:    return toubvec!3(0b001);
      // case riscv_instr_name_t.ECALL:      return toubvec!3(0b000);
      // case riscv_instr_name_t.EBREAK:     return toubvec!3(0b000);
    case riscv_instr_name_t.CSRRW:      return toubvec!3(0b001);
    case riscv_instr_name_t.CSRRS:      return toubvec!3(0b010);
    case riscv_instr_name_t.CSRRC:      return toubvec!3(0b011);
    case riscv_instr_name_t.CSRRWI:     return toubvec!3(0b101);
    case riscv_instr_name_t.CSRRSI:     return toubvec!3(0b110);
    case riscv_instr_name_t.CSRRCI:     return toubvec!3(0b111);
    case riscv_instr_name_t.LWU:        return toubvec!3(0b110);
    case riscv_instr_name_t.LD:         return toubvec!3(0b011);
    case riscv_instr_name_t.SD:         return toubvec!3(0b011);
    case riscv_instr_name_t.ADDIW:      return toubvec!3(0b000);
    case riscv_instr_name_t.SLLIW:      return toubvec!3(0b001);
    case riscv_instr_name_t.SRLIW:      return toubvec!3(0b101);
    case riscv_instr_name_t.SRAIW:      return toubvec!3(0b101);
    case riscv_instr_name_t.ADDW:       return toubvec!3(0b000);
    case riscv_instr_name_t.SUBW:       return toubvec!3(0b000);
    case riscv_instr_name_t.SLLW:       return toubvec!3(0b001);
    case riscv_instr_name_t.SRLW:       return toubvec!3(0b101);
    case riscv_instr_name_t.SRAW:       return toubvec!3(0b101);
    case riscv_instr_name_t.MUL:        return toubvec!3(0b000);
    case riscv_instr_name_t.MULH:       return toubvec!3(0b001);
    case riscv_instr_name_t.MULHSU:     return toubvec!3(0b010);
    case riscv_instr_name_t.MULHU:      return toubvec!3(0b011);
    case riscv_instr_name_t.DIV:        return toubvec!3(0b100);
    case riscv_instr_name_t.DIVU:       return toubvec!3(0b101);
    case riscv_instr_name_t.REM:        return toubvec!3(0b110);
    case riscv_instr_name_t.REMU:       return toubvec!3(0b111);
    case riscv_instr_name_t.MULW:       return toubvec!3(0b000);
    case riscv_instr_name_t.DIVW:       return toubvec!3(0b100);
    case riscv_instr_name_t.DIVUW:      return toubvec!3(0b101);
    case riscv_instr_name_t.REMW:       return toubvec!3(0b110);
    case riscv_instr_name_t.REMUW:      return toubvec!3(0b111);
    case riscv_instr_name_t.ECALL,
      riscv_instr_name_t.EBREAK,
      riscv_instr_name_t.URET,
      riscv_instr_name_t.SRET,
      riscv_instr_name_t.MRET,
      riscv_instr_name_t.DRET,
      riscv_instr_name_t.WFI,
      riscv_instr_name_t.SFENCE_VMA: return toubvec!3(0b000);
    default: uvm_fatal(get_full_name(), format("Unsupported instruction %0s", instr_name));
      assert (false);
    }
  }

  ubvec!7 get_func7() {
    switch (instr_name) {
    case riscv_instr_name_t.SLLI:       return toubvec!7(0b0000000);
    case riscv_instr_name_t.SRLI:       return toubvec!7(0b0000000);
    case riscv_instr_name_t.SRAI:       return toubvec!7(0b0100000);
    case riscv_instr_name_t.ADD:        return toubvec!7(0b0000000);
    case riscv_instr_name_t.SUB:        return toubvec!7(0b0100000);
    case riscv_instr_name_t.SLL:        return toubvec!7(0b0000000);
    case riscv_instr_name_t.SLT:        return toubvec!7(0b0000000);
    case riscv_instr_name_t.SLTU:       return toubvec!7(0b0000000);
    case riscv_instr_name_t.XOR:        return toubvec!7(0b0000000);
    case riscv_instr_name_t.SRL:        return toubvec!7(0b0000000);
    case riscv_instr_name_t.SRA:        return toubvec!7(0b0100000);
    case riscv_instr_name_t.OR:         return toubvec!7(0b0000000);
    case riscv_instr_name_t.AND:        return toubvec!7(0b0000000);
    case riscv_instr_name_t.FENCE:      return toubvec!7(0b0000000);
    case riscv_instr_name_t.FENCE_I:    return toubvec!7(0b0000000);
    case riscv_instr_name_t.SLLIW:      return toubvec!7(0b0000000);
    case riscv_instr_name_t.SRLIW:      return toubvec!7(0b0000000);
    case riscv_instr_name_t.SRAIW:      return toubvec!7(0b0100000);
    case riscv_instr_name_t.ADDW:       return toubvec!7(0b0000000);
    case riscv_instr_name_t.SUBW:       return toubvec!7(0b0100000);
    case riscv_instr_name_t.SLLW:       return toubvec!7(0b0000000);
    case riscv_instr_name_t.SRLW:       return toubvec!7(0b0000000);
    case riscv_instr_name_t.SRAW:       return toubvec!7(0b0100000);
    case riscv_instr_name_t.MUL:        return toubvec!7(0b0000001);
    case riscv_instr_name_t.MULH:       return toubvec!7(0b0000001);
    case riscv_instr_name_t.MULHSU:     return toubvec!7(0b0000001);
    case riscv_instr_name_t.MULHU:      return toubvec!7(0b0000001);
    case riscv_instr_name_t.DIV:        return toubvec!7(0b0000001);
    case riscv_instr_name_t.DIVU:       return toubvec!7(0b0000001);
    case riscv_instr_name_t.REM:        return toubvec!7(0b0000001);
    case riscv_instr_name_t.REMU:       return toubvec!7(0b0000001);
    case riscv_instr_name_t.MULW:       return toubvec!7(0b0000001);
    case riscv_instr_name_t.DIVW:       return toubvec!7(0b0000001);
    case riscv_instr_name_t.DIVUW:      return toubvec!7(0b0000001);
    case riscv_instr_name_t.REMW:       return toubvec!7(0b0000001);
    case riscv_instr_name_t.REMUW:      return toubvec!7(0b0000001);
    case riscv_instr_name_t.ECALL:      return toubvec!7(0b0000000);
    case riscv_instr_name_t.EBREAK:     return toubvec!7(0b0000000);
    case riscv_instr_name_t.URET:       return toubvec!7(0b0000000);
    case riscv_instr_name_t.SRET:       return toubvec!7(0b0001000);
    case riscv_instr_name_t.MRET:       return toubvec!7(0b0011000);
    case riscv_instr_name_t.DRET:       return toubvec!7(0b0111101);
    case riscv_instr_name_t.WFI:        return toubvec!7(0b0001000);
    case riscv_instr_name_t.SFENCE_VMA: return toubvec!7(0b0001001);
    default: uvm_fatal(get_full_name(), format("Unsupported instruction %0s", instr_name));
      assert (false);
    }
  }

  // Convert the instruction to assembly code
  string convert2bin(string prefix = "") {
    import std.conv: to;
    ubvec!32 vec;
    switch (instr_format) {
    case riscv_instr_format_t.J_FORMAT:
      vec = cast(ubvec!1) imm[20]
	~ cast(ubvec!10) imm[1..11]
	~ cast(ubvec!1) imm[11]
	~ cast(ubvec!8) imm[12..20]
	~ toubvec!5(rd)
	~ get_opcode();
      break;
    case riscv_instr_format_t.U_FORMAT:
      vec = cast(ubvec!20) imm[12..32]
	~ toubvec!5(rd)
	~ get_opcode();
      break;
    case riscv_instr_format_t.I_FORMAT:
      if (canFind( [riscv_instr_name_t.FENCE, riscv_instr_name_t.FENCE_I], instr_name)) {
	vec = toubvec!17(0b00000000000000000)
	  ~ get_func3()
	  ~ toubvec!5(0b00000)
	  ~ get_opcode();
      }  // 17 bit zero and 5 bit zero
      else if (category == riscv_instr_category_t.CSR) {
	vec = csr // cast(ubvec!11) csr[0..11] SV BUG?
	  ~ cast(ubvec!5) imm[0..5]
	  ~ get_func3()
	  ~ toubvec!5(rd)
	  ~ get_opcode();
      }
      else if (instr_name == riscv_instr_name_t.ECALL) {
	vec = get_func7()
	  ~ toubvec!18(0b000000000000000000)
	  ~ get_opcode();
      } //  18 bit zero
      else if (canFind([riscv_instr_name_t.URET,
			riscv_instr_name_t.SRET,
			riscv_instr_name_t.MRET], instr_name )) {
	vec = get_func7()
	  ~ toubvec!5(0b00010)
	  ~ toubvec!13(0b0000000000000)
	  ~ get_opcode();
      } // 13 bit zero
      else if (instr_name  ==  riscv_instr_name_t.DRET) {
	vec = get_func7()
	  ~ toubvec!5(0b10010)
	  ~ toubvec!13(0b0000000000000)
	  ~ get_opcode();
      }  // 13 bit zero
      else if (instr_name ==  riscv_instr_name_t.EBREAK) {
	vec = get_func7()
	  ~ toubvec!5(0b00001)
	  ~ toubvec!13(0b0000000000000)
	  ~ get_opcode();
      }  // 13 bit zero
      else if (instr_name == riscv_instr_name_t.WFI) {
	vec = get_func7()
	  ~ toubvec!5(0b00101)
	  ~ toubvec!13(0b0000000000000)
	  ~ get_opcode();
      }
      else {
	vec = cast(ubvec!12) imm[0..12]
	  ~ toubvec!5(rs1)
	  ~ get_func3()
	  ~ toubvec!5(rd)
	  ~ get_opcode();
      }
      break;
    case riscv_instr_format_t.S_FORMAT:
      vec = cast(ubvec!7) imm[5..12]
	~ toubvec!5(rs2)
	~ toubvec!5(rs1)
	~ get_func3()
	~ cast(ubvec!5) imm[0..5]
	~ get_opcode();
      break;
    case riscv_instr_format_t.B_FORMAT:
      vec = cast(ubvec!1) imm[12]
	~ cast(ubvec!6) imm[5..11]
	~ toubvec!5(rs2)
	~ toubvec!5(rs1)
	~ get_func3()
	~ cast(ubvec!4) imm[1..5]
	~ cast(ubvec!1) imm[11]
	~ get_opcode();
      break;
    case riscv_instr_format_t.R_FORMAT:
      if (category == riscv_instr_category_t.CSR) {
	vec = csr // cast(ubvec!11) csr[0..11] -- SV BUG?
	  ~ toubvec!5(rs1)
	  ~ get_func3()
	  ~ toubvec!5(rd)
	  ~ get_opcode();
      }
      else if (instr_name == riscv_instr_name_t.SFENCE_VMA) {
	vec = get_func7()
	  ~ toubvec!18(0b000000000000000000)
	  ~ get_opcode();
      } // 18 bits zero
      else {
	vec = get_func7()
	  ~ toubvec!5(rs2)
	  ~ toubvec!5(rs1)
	  ~ get_func3()
	  ~ toubvec!5(rd)
	  ~ get_opcode();
      }
      break;
    default: uvm_fatal(get_full_name(), format("Unsupported format %0s", instr_format));
      assert (false);
    }
    return prefix ~ format("%8h", vec);
  }

  string get_instr_name() {
    import std.conv: to;
    import std.array: replace;
    string str_instr_name = instr_name.to!string();
    return str_instr_name.replace( '_', '.');
  }

  // // Get RVC register name for CIW, CL, CS, CB format
  ubvec!3  get_c_gpr(riscv_reg_t gpr) {
    ubvec!8 c_gpr = toubvec!8(gpr);
    return cast(ubvec!3) c_gpr[0..3];
  }

  // // Default return imm value directly, can be overriden to use labels and symbols
  // // Example: %hi(symbol), %pc_rel(label) ...
  string get_imm() {
    return imm_str;
  }

  void clear_unused_label() {
    if (has_label && !is_branch_target && is_local_numeric_label) {
      has_label = false;
    }
  }

  override void do_copy(uvm_object rhs) {
    riscv_instr rhs_;
    super.copy(rhs);
    rhs_ = cast(riscv_instr) rhs;
    if ( rhs_ !is null ) { //rhs_ = rhs;
      this.group          = rhs_.group;
      this.instr_format   = rhs_.instr_format;
      this.category       = rhs_.category;
      this.instr_name     = rhs_.instr_name;
      this.rs2            = rhs_.rs2;
      this.rs1            = rhs_.rs1;
      this.rd             = rhs_.rd;
      this.imm            = rhs_.imm;
      this.imm_type       = rhs_.imm_type;
      this.imm_len        = rhs_.imm_len;
      this.imm_mask       = rhs_.imm_mask;
      this.imm_str        = rhs_.imm_str;
      this.imm_mask       = rhs_.imm_mask;
      this.is_compressed  = rhs_.is_compressed;
      this.has_rs2        = rhs_.has_rs2;
      this.has_rs1        = rhs_.has_rs1;
      this.has_rd         = rhs_.has_rd;
      this.has_imm        = rhs_.has_imm;
    }
  }

  void update_imm_str() {
    imm_str = format("%0d", cast(bvec!32) imm);
  }

  //`include "isa/riscv_instr_cov.svh"

}
