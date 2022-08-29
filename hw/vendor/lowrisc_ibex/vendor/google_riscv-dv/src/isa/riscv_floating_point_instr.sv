/*
 * Copyright 2020 Google LLC
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

class riscv_floating_point_instr extends riscv_instr;

  rand riscv_fpr_t fs1;
  rand riscv_fpr_t fs2;
  rand riscv_fpr_t fs3;
  rand riscv_fpr_t fd;
  rand f_rounding_mode_t rm;
  rand bit use_rounding_mode_from_instr;
  bit              has_fs1 = 1'b1;
  bit              has_fs2 = 1'b1;
  bit              has_fs3 = 1'b0;
  bit              has_fd  = 1'b1;

  `uvm_object_utils(riscv_floating_point_instr)
  `uvm_object_new

  constraint rvfc_csr_c {
    if (format inside {CL_FORMAT, CS_FORMAT, CI_FORMAT, CSS_FORMAT}) {
      if (has_rs1) {
        rs1 inside {[S0:A5]};
      }
      if (has_fs2) {
        fs2 inside {[FS0:FS1]};
      }
      if (has_fd) {
        fd inside {[FA0:FA5]};
      }
    }
}
  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    case (format)
      I_FORMAT:
        if (category == LOAD) begin
          asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fd.name(), get_imm(), rs1.name());
        end else if (instr_name inside {FMV_X_W, FMV_X_D, FCVT_W_S, FCVT_WU_S,
                                        FCVT_L_S, FCVT_LU_S, FCVT_L_D, FCVT_LU_D,
                                        FCVT_W_D, FCVT_WU_D}) begin
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), fs1.name());
        end else if (instr_name inside {FMV_W_X, FMV_D_X, FCVT_S_W, FCVT_S_WU,
                                        FCVT_S_L, FCVT_D_L, FCVT_S_LU, FCVT_D_W,
                                        FCVT_D_LU, FCVT_D_WU}) begin
          asm_str = $sformatf("%0s%0s, %0s", asm_str, fd.name(), rs1.name());
        end else begin
          asm_str = $sformatf("%0s%0s, %0s", asm_str, fd.name(), fs1.name());
        end
      S_FORMAT:
        asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fs2.name(), get_imm(), rs1.name());
      R_FORMAT:
        if (category == COMPARE) begin
          asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rd.name(), fs1.name(), fs2.name());
        end else if (instr_name inside {FCLASS_S, FCLASS_D}) begin
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), fs1.name());
        end else begin
          asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, fd.name(), fs1.name(), fs2.name());
        end
      R4_FORMAT:
        asm_str = $sformatf("%0s%0s, %0s, %0s, %0s", asm_str, fd.name(), fs1.name(),
                                                     fs2.name(), fs3.name());
      CL_FORMAT:
        asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fd.name(), get_imm(), rs1.name());
      CS_FORMAT:
        asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fs2.name(), get_imm(), rs1.name());
      CSS_FORMAT:
        asm_str = $sformatf("%0s%0s, %0s(sp)", asm_str, fs2.name(), get_imm());
      CI_FORMAT:
        asm_str = $sformatf("%0s%0s, %0s", asm_str, fd.name(), get_imm());
      default:
        `uvm_fatal(`gfn, $sformatf("Unsupported floating point format: %0s", format.name()))
    endcase
    if ((category == ARITHMETIC) && use_rounding_mode_from_instr &&
        !(instr_name inside {FMIN_S, FMAX_S, FMIN_D, FMAX_D, FMV_W_X, FMV_X_W,
                             FMV_D_X, FMV_X_D, FCLASS_S, FCLASS_D,
                             FCVT_D_S, FCVT_D_W, FCVT_D_WU,
                             FSGNJ_S, FSGNJN_S, FSGNJX_S, FSGNJ_D, FSGNJN_D, FSGNJX_D})) begin
      asm_str = {asm_str, ", ", rm.name()};
    end
    if(comment != "")
      asm_str = {asm_str, " #",comment};
    return asm_str.tolower();
  endfunction

  virtual function void set_imm_len();
    if (format inside {CL_FORMAT, CS_FORMAT})
      imm_len = 5;
    if (format inside {CI_FORMAT, CSS_FORMAT})
      imm_len = 6;
  endfunction: set_imm_len

  virtual function void do_copy(uvm_object rhs);
    riscv_floating_point_instr rhs_;
    super.copy(rhs);
    assert($cast(rhs_, rhs));
    this.fs3     = rhs_.fs3;
    this.fs2     = rhs_.fs2;
    this.fs1     = rhs_.fs1;
    this.fd      = rhs_.fd;
    this.has_fs3 = rhs_.has_fs3;
    this.has_fs2 = rhs_.has_fs2;
    this.has_fs1 = rhs_.has_fs1;
    this.has_fd  = rhs_.has_fd;
  endfunction : do_copy

  virtual function void set_rand_mode();
    has_rs1 = 0;
    has_rs2 = 0;
    has_rd  = 0;
    has_imm = 0;
    case (format)
      I_FORMAT: begin
        has_fs2 = 1'b0;
        if (category == LOAD) begin
          has_imm = 1'b1;
        end else if (instr_name inside {FMV_X_W, FMV_X_D, FCVT_W_S, FCVT_WU_S,
                                        FCVT_L_S, FCVT_LU_S, FCVT_L_D, FCVT_LU_D, FCVT_LU_S,
                                        FCVT_W_D, FCVT_WU_D}) begin
          has_fd = 1'b0;
          has_rd = 1'b1;
        end else if (instr_name inside {FMV_W_X, FMV_D_X, FCVT_S_W, FCVT_S_WU,
                                        FCVT_S_L, FCVT_D_L, FCVT_S_LU, FCVT_D_W,
                                        FCVT_D_LU, FCVT_D_WU}) begin
          has_rs1 = 1'b1;
          has_fs1 = 1'b0;
        end
      end
      S_FORMAT: begin
        has_imm = 1'b1;
        has_rs1 = 1'b1;
        has_fs1 = 1'b0;
        has_fs3 = 1'b0;
      end
      R_FORMAT:
        if (category == COMPARE) begin
          has_rd = 1'b1;
          has_fd = 1'b0;
        end else if (instr_name inside {FCLASS_S, FCLASS_D}) begin
          has_rd = 1'b1;
          has_fd = 1'b0;
          has_fs2 = 1'b0;
        end
      R4_FORMAT: begin
        has_fs3 = 1'b1;
      end
      CL_FORMAT: begin
        has_imm = 1'b1;
        has_rs1 = 1'b1;
        has_fs1 = 1'b0;
        has_fs2 = 1'b0;
      end
      CS_FORMAT: begin
        has_imm = 1'b1;
        has_rs1 = 1'b1;
        has_fs1 = 1'b0;
        has_fd = 1'b0;
      end
      CSS_FORMAT: begin
        has_rs1 = 1'b0;
        has_fd = 1'b0;
      end
      CI_FORMAT: begin
        has_rs1 = 1'b0;
        has_fs2 = 1'b0;
      end
      default: `uvm_info(`gfn, $sformatf("Unsupported format %0s", format.name()), UVM_LOW)
    endcase
  endfunction

  function void pre_randomize();
    super.pre_randomize();
    fs1.rand_mode(has_fs1);
    fs2.rand_mode(has_fs2);
    fs3.rand_mode(has_fs3);
    fd.rand_mode(has_fd);
  endfunction

  // coverage related functons
  virtual function void update_src_regs(string operands[$]);
    if(category inside {LOAD, CSR}) begin
      super.update_src_regs(operands);
      return;
    end
    case(format)
      I_FORMAT: begin
        // TODO ovpsim has an extra operand rte as below
        // fcvt.d.s fs1,fs4,rte
        //`DV_CHECK_FATAL(operands.size() == 2)
        if (has_fs1) begin
          fs1 = get_fpr(operands[1]);
          fs1_value = get_gpr_state(operands[1]);
        end else if (has_rs1) begin
          rs1 = get_gpr(operands[1]);
          rs1_value = get_gpr_state(operands[1]);
        end
      end
      S_FORMAT: begin
        `DV_CHECK_FATAL(operands.size() == 3)
        // FSW rs2 is fp
        fs2 = get_fpr(operands[0]);
        fs2_value = get_gpr_state(operands[0]);
        rs1 = get_gpr(operands[1]);
        rs1_value = get_gpr_state(operands[1]);
        get_val(operands[2], imm);
      end
      R_FORMAT: begin
        // convert Pseudoinstructions for ovpsim
        // fmv.s rd, rs -> fsgnj.s rd, rs, rs
        if (operands.size() == 2 && instr_name inside {FSGNJ_S, FSGNJX_S, FSGNJN_S, FSGNJ_D,
                                                       FSGNJX_D, FSGNJN_D}) begin
          operands.push_back(operands[$]);
        end

        if (has_fs2 || category == CSR) begin
          `DV_CHECK_FATAL(operands.size() == 3)
        end else begin
          `DV_CHECK_FATAL(operands.size() == 2)
        end
        if(category != CSR) begin
          fs1 = get_fpr(operands[1]);
          fs1_value = get_gpr_state(operands[1]);
          if (has_fs2) begin
            fs2 = get_fpr(operands[2]);
            fs2_value = get_gpr_state(operands[2]);
          end
        end
      end
      R4_FORMAT: begin
        `DV_CHECK_FATAL(operands.size() == 4)
        fs1 = get_fpr(operands[1]);
        fs1_value = get_gpr_state(operands[1]);
        fs2 = get_fpr(operands[2]);
        fs2_value = get_gpr_state(operands[2]);
        fs3 = get_fpr(operands[3]);
        fs3_value = get_gpr_state(operands[3]);
      end
      default: `uvm_fatal(`gfn, $sformatf("Unsupported format %0s", format))
    endcase
  endfunction : update_src_regs

  virtual function void update_dst_regs(string reg_name, string val_str);
    get_val(val_str, gpr_state[reg_name], .hex(1));
    if (has_fd) begin
      fd = get_fpr(reg_name);
      fd_value = get_gpr_state(reg_name);
    end else if (has_rd) begin
      rd = get_gpr(reg_name);
      rd_value = get_gpr_state(reg_name);
    end
  endfunction : update_dst_regs

  virtual function riscv_fpr_t get_fpr(input string str);
    str = str.toupper();
    if (!uvm_enum_wrapper#(riscv_fpr_t)::from_name(str, get_fpr)) begin
      `uvm_fatal(`gfn, $sformatf("Cannot convert %0s to FPR", str))
    end
  endfunction : get_fpr

  virtual function void pre_sample();
    super.pre_sample();

    // for single precision sign bit is bit 31, upper 32 bits are all 1s
    // for double precision, it's 63
    if (group inside {RV32F, RV64F}) begin
      fs1_sign = get_fp_operand_sign(fs1_value, 31);
      fs2_sign = get_fp_operand_sign(fs2_value, 31);
      fs3_sign = get_fp_operand_sign(fs3_value, 31);
      fd_sign = get_fp_operand_sign(fd_value, 31);
    end else if (instr_name == FCVT_S_D) begin
      fs1_sign = get_fp_operand_sign(fs1_value, 63);
      fd_sign = get_fp_operand_sign(fd_value, 31);
    end else if (instr_name == FCVT_D_S) begin
      fs1_sign = get_fp_operand_sign(fs1_value, 31);
      fd_sign = get_fp_operand_sign(fd_value, 63);
    end else begin
      fs1_sign = get_fp_operand_sign(fs1_value, 63);
      fs2_sign = get_fp_operand_sign(fs2_value, 63);
      fs3_sign = get_fp_operand_sign(fs3_value, 63);
      fd_sign = get_fp_operand_sign(fd_value, 63);
    end
  endfunction : pre_sample

  virtual function operand_sign_e get_fp_operand_sign(bit [XLEN-1:0] value, int idx);
    if (value[idx]) begin
      return NEGATIVE;
    end else begin
      return POSITIVE;
    end
  endfunction

  virtual function void check_hazard_condition(riscv_instr pre_instr);
    riscv_floating_point_instr pre_fp_instr;
    super.check_hazard_condition(pre_instr);
    if ($cast(pre_fp_instr, pre_instr) && pre_fp_instr.has_fd) begin
      if ((has_fs1 && (fs1 == pre_fp_instr.fd)) || (has_fs2 && (fs2 == pre_fp_instr.fd))
          || (has_fs3 && (fs3 == pre_fp_instr.fd))) begin
        gpr_hazard = RAW_HAZARD;
      end else if (has_fd && (fd == pre_fp_instr.fd)) begin
        gpr_hazard = WAW_HAZARD;
      end else if (has_fd && ((pre_fp_instr.has_fs1 && (pre_fp_instr.fs1 == fd)) ||
                              (pre_fp_instr.has_fs2 && (pre_fp_instr.fs2 == fd)) ||
                              (pre_fp_instr.has_fs3 && (pre_fp_instr.fs3 == fd)))) begin
        gpr_hazard = WAR_HAZARD;
      end else begin
        gpr_hazard = NO_HAZARD;
      end
    end
  endfunction
endclass
