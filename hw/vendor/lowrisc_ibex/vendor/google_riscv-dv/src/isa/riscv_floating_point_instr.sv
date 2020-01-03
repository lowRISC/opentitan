class riscv_floating_point_instr extends riscv_instr;

  rand riscv_fpr_t fs1;
  rand riscv_fpr_t fs2;
  rand riscv_fpr_t fs3;
  rand riscv_fpr_t fd;

  `uvm_object_utils(riscv_floating_point_instr)

  function new(string name = "");
    super.new(name);
    rs2.rand_mode(0);
  endfunction

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
    this.fs3            = rhs_.fs3;
    this.fs2            = rhs_.fs2;
    this.fs1            = rhs_.fs1;
    this.fd             = rhs_.fd;
  endfunction : do_copy

endclass
