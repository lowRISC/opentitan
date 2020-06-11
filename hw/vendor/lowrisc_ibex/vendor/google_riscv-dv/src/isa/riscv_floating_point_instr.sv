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
  bit              has_fs1 = 1'b1;
  bit              has_fs2 = 1'b1;
  bit              has_fs3 = 1'b0;
  bit              has_fd  = 1'b1;

  `uvm_object_utils(riscv_floating_point_instr)
  `uvm_object_new

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    case (format)
      I_FORMAT:
        if (category == LOAD) begin
          asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fd.name(), get_imm(), rs1.name());
        end else if (instr_name inside {FMV_X_W, FMV_X_D, FCVT_W_S, FCVT_WU_S,
                                        FCVT_L_S, FCVT_LU_S, FCVT_L_D, FCVT_LU_D, FCVT_LU_S,
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
      default:
        `uvm_fatal(`gfn, $sformatf("Unsupported floating point format: %0s", format.name()))
    endcase
    if(comment != "")
      asm_str = {asm_str, " #",comment};
    return asm_str.tolower();
  endfunction

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
        `DV_CHECK_FATAL(operands.size() == 2)
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
        rs1 = get_gpr(operands[2]);
        rs1_value = get_gpr_state(operands[2]);
        get_val(operands[1], imm);
      end
      R_FORMAT: begin
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
    $display("update_dst_regs %0s", reg_name);
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
    if (!fpr_enum::from_name(str, get_fpr)) begin
      `uvm_fatal(`gfn, $sformatf("Cannot convert %0s to FPR", str))
    end
  endfunction : get_fpr

endclass
