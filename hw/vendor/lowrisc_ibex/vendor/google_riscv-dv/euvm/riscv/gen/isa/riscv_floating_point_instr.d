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

module riscv.gen.isa.riscv_floating_point_instr;

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

class riscv_floating_point_instr: riscv_instr
{
  mixin uvm_object_utils;

  @rand riscv_fpr_t fs1;
  @rand riscv_fpr_t fs2;
  @rand riscv_fpr_t fs3;
  @rand riscv_fpr_t fd;
  @rand f_rounding_mode_t rm;
  @rand bool use_rounding_mode_from_instr;

  bool              has_fs1 = true;
  bool              has_fs2 = true;
  bool              has_fs3 = false;
  bool              has_fd  = true;


  this(string name = "") {
    super(name);
  }


  // Convert the instruction to assembly code
  override string convert2asm(string prefix = "") {
    import std.conv: to;
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    switch (instr_format) {
    case riscv_instr_format_t.I_FORMAT:
      if (category == riscv_instr_category_t.LOAD) {
	asm_str = format("%0s%0s, %0s(%0s)", asm_str, fd, get_imm(), rs1);
      }
      else if (instr_name.inside (riscv_instr_name_t.FMV_X_W,
				  riscv_instr_name_t.FMV_X_D,
				  riscv_instr_name_t.FCVT_W_S,
				  riscv_instr_name_t.FCVT_WU_S,
				  riscv_instr_name_t.FCVT_L_S,
				  riscv_instr_name_t.FCVT_LU_S,
				  riscv_instr_name_t.FCVT_L_D,
				  riscv_instr_name_t.FCVT_LU_D,
				  riscv_instr_name_t.FCVT_W_D,
				  riscv_instr_name_t.FCVT_WU_D)) {
	asm_str = format("%0s%0s, %0s", asm_str, rd, fs1);
      }
      else if (instr_name.inside(riscv_instr_name_t.FMV_W_X,
				 riscv_instr_name_t.FMV_D_X,
				 riscv_instr_name_t.FCVT_S_W,
				 riscv_instr_name_t.FCVT_S_WU,
				 riscv_instr_name_t.FCVT_S_L,
				 riscv_instr_name_t.FCVT_D_L,
				 riscv_instr_name_t.FCVT_S_LU,
				 riscv_instr_name_t.FCVT_D_W,
				 riscv_instr_name_t.FCVT_D_LU,
				 riscv_instr_name_t.FCVT_D_WU)) {
	asm_str = format("%0s%0s, %0s", asm_str, fd, rs1);
      }
      else {
	asm_str = format("%0s%0s, %0s", asm_str, fd, fs1);
      }
      break;
    case riscv_instr_format_t.S_FORMAT:
      asm_str = format("%0s%0s, %0s(%0s)", asm_str, fs2, get_imm(), rs1);
      break;
    case riscv_instr_format_t.R_FORMAT:
      if (category == riscv_instr_category_t.COMPARE) {
	asm_str = format("%0s%0s, %0s, %0s", asm_str, rd, fs1, fs2);
      }
      else if (instr_name.inside(riscv_instr_name_t.FCLASS_S, riscv_instr_name_t.FCLASS_D)) {
	asm_str = format("%0s%0s, %0s", asm_str, rd, fs1);
      }
      else {
	asm_str = format("%0s%0s, %0s, %0s", asm_str, fd, fs1, fs2);
      }
      break;
    case riscv_instr_format_t.R4_FORMAT:
      asm_str = format("%0s%0s, %0s, %0s, %0s", asm_str, fd, fs1, fs2, fs3);
      break;
    case riscv_instr_format_t.CL_FORMAT:
      asm_str = format("%0s%0s, %0s(%0s)", asm_str, fd, get_imm(), rs1);
      break;
    case riscv_instr_format_t.CS_FORMAT:
      asm_str = format("%0s%0s, %0s(%0s)", asm_str, fs2, get_imm(), rs1);
      break;
    default:
      uvm_fatal(get_full_name(), format("Unsupported floating point format: %0s", instr_format));
    }
    if ((category == riscv_instr_category_t.ARITHMETIC) && use_rounding_mode_from_instr &&
        !(instr_name.inside(riscv_instr_name_t.FMIN_S, riscv_instr_name_t.FMAX_S,
			    riscv_instr_name_t.FMIN_D, riscv_instr_name_t.FMAX_D,
			    riscv_instr_name_t.FMV_W_X, riscv_instr_name_t.FMV_X_W,
			    riscv_instr_name_t.FMV_D_X, riscv_instr_name_t.FMV_X_D,
			    riscv_instr_name_t.FCLASS_S, riscv_instr_name_t.FCLASS_D,
			    riscv_instr_name_t.FCVT_D_S, riscv_instr_name_t.FCVT_D_W,
			    riscv_instr_name_t.FCVT_D_WU, riscv_instr_name_t.FSGNJ_S,
			    riscv_instr_name_t.FSGNJN_S, riscv_instr_name_t.FSGNJX_S,
			    riscv_instr_name_t.FSGNJ_D, riscv_instr_name_t.FSGNJN_D,
			    riscv_instr_name_t.FSGNJX_D))) {
      asm_str ~= ", " ~ rm.to!string();
    }
    if(comment != "") {
      asm_str ~= " #" ~ comment;
    }
    return asm_str.toLower();
  }

  override void do_copy(uvm_object rhs) {
    riscv_floating_point_instr rhs_;
    super.copy(rhs);
    rhs_ = cast(riscv_floating_point_instr) rhs;
    if (rhs_ is null) {
      assert (false);
    }
    else {
      this.fs3     = rhs_.fs3;
      this.fs2     = rhs_.fs2;
      this.fs1     = rhs_.fs1;
      this.fd      = rhs_.fd;
      this.has_fs3 = rhs_.has_fs3;
      this.has_fs2 = rhs_.has_fs2;
      this.has_fs1 = rhs_.has_fs1;
      this.has_fd  = rhs_.has_fd;
    }
  }

  override void set_rand_mode() {
    has_rs1 = false;
    has_rs2 = false;
    has_rd  = false;
    has_imm = false;
    switch (instr_format) {
    case riscv_instr_format_t.I_FORMAT:
      has_fs2 = false;
      if (category == riscv_instr_category_t.LOAD) {
	has_imm = true;
      }
      else if (instr_name.inside(riscv_instr_name_t.FMV_X_W,
				 riscv_instr_name_t.FMV_X_D,
				 riscv_instr_name_t.FCVT_W_S,
				 riscv_instr_name_t.FCVT_WU_S,
				 riscv_instr_name_t.FCVT_L_S,
				 riscv_instr_name_t.FCVT_LU_S,
				 riscv_instr_name_t.FCVT_L_D,
				 riscv_instr_name_t.FCVT_LU_D,
				 riscv_instr_name_t.FCVT_LU_S,
				 riscv_instr_name_t.FCVT_W_D,
				 riscv_instr_name_t.FCVT_WU_D)) {
	has_fd = false;
	has_rd = true;
      }
      else if (instr_name.inside(riscv_instr_name_t.FMV_W_X,
				 riscv_instr_name_t.FMV_D_X,
				 riscv_instr_name_t.FCVT_S_W,
				 riscv_instr_name_t.FCVT_S_WU,
				 riscv_instr_name_t.FCVT_S_L,
				 riscv_instr_name_t.FCVT_D_L,
				 riscv_instr_name_t.FCVT_S_LU,
				 riscv_instr_name_t.FCVT_D_W,
				 riscv_instr_name_t.FCVT_D_LU,
				 riscv_instr_name_t.FCVT_D_WU)) {
	has_rs1 = true;
	has_fs1 = false;
      }
      break;
    case riscv_instr_format_t.S_FORMAT:
      has_imm = true;
      has_rs1 = true;
      has_fs1 = false;
      has_fs3 = false;
      break;
    case riscv_instr_format_t.R_FORMAT:
      if (category == riscv_instr_category_t.COMPARE) {
	has_rd = true;
	has_fd = false;
      }
      else if (instr_name.inside(riscv_instr_name_t.FCLASS_S,
				 riscv_instr_name_t.FCLASS_D)) {
	has_rd = true;
	has_fd = false;
	has_fs2 = false;
      }
      break;
    case riscv_instr_format_t.R4_FORMAT:
      has_fs3 = true;
      break;
    case riscv_instr_format_t.CL_FORMAT:
      has_imm = true;
      has_rs1 = true;
      has_fs1 = false;
      has_fs2 = false;
      break;
    case riscv_instr_format_t.CS_FORMAT:
      has_imm = true;
      has_rs1 = true;
      has_fs1 = false;
      has_fd = false;
      break;
    default: uvm_info(get_full_name() , format("Unsupported format %0s", instr_format), UVM_LOW);
    }
  }

  override void pre_randomize() {
    super.pre_randomize();
    rand_mode!q{fs1}(has_fs1);
    rand_mode!q{fs2}(has_fs2);
    rand_mode!q{fs3}(has_fs3);
    rand_mode!q{fd}(has_fd);
  }

  // coverage related functons
  // override void update_src_regs(string [] operands) {
  //   if(category.inside(riscv_instr_category_t.LOAD, riscv_instr_category_t.CSR)) {
  // 	// commented as we are not incluing coverage now.
  // 	//	super.update_src_regs(operands);
  // 	return;
  //     }
  //   switch (instr_format) {
  //     case riscv_instr_format_t.I_FORMAT:
  // 	  // TODO ovpsim has an extra operand rte as below
  // 	  // fcvt.d.s fs1,fs4,rte
  // 	  //`DV_CHECK_FATAL(operands.size() == 2)
  // 	  assert(operands.length == 2);
  // 	  if (has_fs1) {
  // 	      fs1 = get_fpr(operands[1]);
  // 	      fs1_value = get_gpr_state(operands[1]);
  // 	    } else if (has_rs1) {
  // 	      rs1 = get_gpr(operands[1]);
  // 	      rs1_value = get_gpr_state(operands[1]);
  // 	    }
  // 	  break;
  //     case riscv_instr_format_t.S_FORMAT:
  // 	  //DV_CHECK_FATAL(operands.size() == 3)
  // 	  // FSW rs2 is fp
  // 	  assert(operands.size() == 3);
  // 	  fs2 = get_fpr(operands[0]);
  // 	  fs2_value = get_gpr_state(operands[0]);
  // 	  rs1 = get_gpr(operands[2]);
  // 	  rs1_value = get_gpr_state(operands[2]);
  // 	  get_val(operands[1], imm);
  // 	  break;
  //     case riscv_instr_format_t.R_FORMAT:
  // 	  // convert Pseudoinstructions for ovpsim
  // 	  // fmv.s rd, rs -> fsgnj.s rd, rs, rs
  // 	  if (operands.size() == 2 && (canFind([riscv_instr_name_t.FSGNJ_S,
  // 						riscv_instr_name_t.FSGNJX_S,
  // 						riscv_instr_name_t.FSGNJN_S,
  // 						riscv_instr_name_t.FSGNJ_D,
  // 						riscv_instr_name_t.FSGNJX_D,
  // 						riscv_instr_name_t.FSGNJN_D], instr_name))) {
  // 	      int len = operands.length();
  // 	      //operands.push_back(operands[$]);
  // 	      operands[len] = operands[$];
  // 	    }

  // 	  if (has_fs2 || category == riscv_instr_category_t.CSR) {
  // 	      //`DV_CHECK_FATAL(operands.size() == 3)
  // 	      assert( operands.size() == 3);
  // 	    }
  // 	  else
  // 	    {
  // 	      //  `DV_CHECK_FATAL(operands.size() == 2)
  // 	      assert( operands.size() == 2);
  // 	    }
  // 	  if(category != riscv_instr_category_t.CSR) {
  // 	      fs1 = get_fpr(operands[1]);
  // 	      fs1_value = get_gpr_state(operands[1]);
  // 	      if (has_fs2) {
  // 		  fs2_value = get_fpr(operands[2]);
  // 		  fs2_value = get_gpr_state(operands[2]);
  // 		}
  // 	    }
  // 	  break;
  //     case riscv_instr_format_t.R4_FORMAT:
  // 	  //`DV_CHECK_FATAL(operands.size() == 4)
  // 	  assert (operands.length == 4);
  // 	  fs1 = get_fpr(operands[1]);
  // 	  fs1_value = get_gpr_state(operands[1]);
  // 	  fs2 = get_fpr(operands[2]);
  // 	  fs2_value = get_gpr_state(operands[2]);
  // 	  fs3 = get_fpr(operands[3]);
  // 	  fs3_value = get_gpr_state(operands[3]);
  // 	  break;
  //     default: uvm_fatal(get_full_name(), format("Unsupported format %0s", instr_format));
  //     }
  // }

  // void update_dst_regs(string reg_name, string val_str) {
  //   get_val(val_str, gpr_state[reg_name], true);
  //   if (has_fd) {
  // 	fd = get_fpr(reg_name);
  // 	fd_value = get_gpr_state(reg_name);
  //     }
  //   else if (has_rd) {
  // 	rd = get_gpr(reg_name);
  // 	rd_value = get_gpr_state(reg_name);
  //     }
  // }

  // riscv_fpr_t get_fpr(in string str) {
  //   str = str.toUpper();
  //   if (!uvm_enum_wrapper!(riscv_fpr_t).from_name(str, get_fpr)) {
  // 	uvm_fatal(get_full_name(), format("Cannot convert %0s to FPR", str));
  //     }
  // }

  // void pre_sample()
  // {
  //   super.pre_sample();

  //   // for single precision sign bit is bit 31, upper 32 bits are all 1s
  //   // for double precision, it's 63
  //   if (canFind((riscv_instr_group_t.RV32F, riscv_instr_group_t.RV64F), group))
  //     {
  // 	fs1_sign = get_fp_operand_sign(fs1_value, 31);
  // 	fs2_sign = get_fp_operand_sign(fs2_value, 31);
  // 	fs3_sign = get_fp_operand_sign(fs3_value, 31);
  // 	fd_sign = get_fp_operand_sign(fd_value, 31);
  //     }
  //   else if (instr_name == riscv_instr_name_t.FCVT_S_D)
  //     {
  // 	fs1_sign = get_fp_operand_sign(fs1_value, 63);
  // 	fd_sign = get_fp_operand_sign(fd_value, 31);
  //     }
  //   else if (instr_name == riscv_instr_name_t.FCVT_D_S)
  //     {
  // 	fs1_sign = get_fp_operand_sign(fs1_value, 31);
  // 	fd_sign = get_fp_operand_sign(fd_value, 63);
  //     }
  //   else
  //     {
  // 	fs1_sign = get_fp_operand_sign(fs1_value, 63);
  // 	fs2_sign = get_fp_operand_sign(fs2_value, 63);
  // 	fs3_sign = get_fp_operand_sign(fs3_value, 63);
  // 	fd_sign = get_fp_operand_sign(fd_value, 63);
  //     }
  // }

  // operand_sign_e get_fp_operand_sign(ubvec!XLEN value, int idx)
  // {
  //   if (value[idx])
  //     {
  // 	return operand_sign_e.NEGATIVE;
  //     }
  //   else
  //     {
  // 	return operand_sign_e.POSITIVE;
  //     }
  // }

  // override void check_hazard_condition(riscv_instr pre_instr)
  // {
  //   riscv_floating_point_instr pre_fp_instr;
  //   super.check_hazard_condition(pre_instr);
  //   pre_fp_instr = cast(riscv_floating_point_instr) pre_instr;

  //   if (pre_fp_instr != null && pre_fp_instr.has_fd)
  //     {
  // 	if ((has_fs1 && (fs1 == pre_fp_instr.fd)) || (has_fs2 && (fs2 == pre_fp_instr.fd))
  // 	    || (has_fs3 && (fs3 == pre_fp_instr.fd)))
  // 	  {
  // 	    gpr_hazard = hazard_e.RAW_HAZARD;
  // 	  }
  // 	else if (has_fd && (fd == pre_fp_instr.fd))
  // 	  {
  // 	    gpr_hazard = hazard_e.WAW_HAZARD;
  // 	  }
  // 	else if (has_fd && ((pre_fp_instr.has_fs1 && (pre_fp_instr.fs1 == fd)) ||
  // 			    (pre_fp_instr.has_fs2 && (pre_fp_instr.fs2 == fd)) ||
  // 			    (pre_fp_instr.has_fs3 && (pre_fp_instr.fs3 == fd))))
  // 	  {
  // 	    gpr_hazard = hazard_e.WAR_HAZARD;
  // 	  }
  // 	else
  // 	  {
  // 	    gpr_hazard = hazard_e.NO_HAZARD;
  // 	  }
  //     }

  // }

}
