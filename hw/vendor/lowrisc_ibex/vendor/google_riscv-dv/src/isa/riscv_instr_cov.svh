
  typedef uvm_enum_wrapper#(riscv_reg_t) gpr_enum;
  typedef uvm_enum_wrapper#(riscv_fpr_t) fpr_enum;
  typedef uvm_enum_wrapper#(privileged_reg_t) preg_enum;

  typedef enum bit[1:0] {
    POSITIVE, NEGATIVE
  } operand_sign_e;

  typedef enum bit[1:0] {
    DIV_NORMAL, DIV_BY_ZERO, DIV_OVERFLOW
  } div_result_e;

  typedef enum bit[1:0] {
    EQUAL, LARGER, SMALLER
  } compare_result_e;

  typedef enum bit [1:0] {
    IDENTICAL, OPPOSITE, SIMILAR, DIFFERENT
  } logical_similarity_e;

  typedef enum bit[2:0] {
    NORMAL_VAL, MIN_VAL, MAX_VAL, ZERO_VAL
  } special_val_e;

  static bit [XLEN-1:0] gpr_state[string];

  rand bit [XLEN-1:0]   rs1_value;
  rand bit [XLEN-1:0]   rs2_value;
  rand bit [XLEN-1:0]   rs3_value;
  rand bit [XLEN-1:0]   rd_value;
  rand bit [XLEN-1:0]   fs1_value;
  rand bit [XLEN-1:0]   fs2_value;
  rand bit [XLEN-1:0]   fs3_value;
  rand bit [XLEN-1:0]   fd_value;
  bit [31:0]            binary;
  bit [XLEN-1:0]        pc;
  bit [XLEN-1:0]        mem_addr;

  bit                   unaligned_pc;
  bit                   unaligned_mem_access;
  bit                   compressed;
  bit                   branch_hit;
  div_result_e          div_result;
  operand_sign_e        rs1_sign;
  operand_sign_e        rs2_sign;
  operand_sign_e        rs3_sign;
  operand_sign_e        fs1_sign;
  operand_sign_e        fs2_sign;
  operand_sign_e        fs3_sign;
  operand_sign_e        imm_sign;
  operand_sign_e        rd_sign;
  operand_sign_e        fd_sign;
  hazard_e              gpr_hazard;
  hazard_e              lsu_hazard;
  special_val_e         rs1_special_val;
  special_val_e         rs2_special_val;
  special_val_e         rs3_special_val;
  special_val_e         rd_special_val;
  special_val_e         imm_special_val;
  compare_result_e      compare_result;
  logical_similarity_e  logical_similarity;
  string                trace;

  `VECTOR_INCLUDE("riscv_instr_cov_item_inc_declares.sv")

  virtual function void pre_sample();
    unaligned_pc = (pc[1:0] != 2'b00);
    rs1_sign = get_operand_sign(rs1_value);
    rs2_sign = get_operand_sign(rs2_value);
    rs3_sign = get_operand_sign(rs3_value);
    rd_sign = get_operand_sign(rd_value);
    fs1_sign = get_operand_sign(fs1_value);
    fs2_sign = get_operand_sign(fs2_value);
    fs3_sign = get_operand_sign(fs2_value);
    fd_sign = get_operand_sign(fd_value);
    imm_sign = get_imm_sign(imm);
    rs1_special_val = get_operand_special_val(rs1_value);
    rd_special_val = get_operand_special_val(rd_value);
    rs2_special_val = get_operand_special_val(rs2_value);
    rs3_special_val = get_operand_special_val(rs3_value);
    if ((format != R_FORMAT) && (format != CR_FORMAT)) begin
      imm_special_val = get_imm_special_val(imm);
    end
    if (category inside {COMPARE, BRANCH}) begin
      compare_result = get_compare_result();
    end
    if (category inside {LOAD, STORE}) begin
      mem_addr = rs1_value + imm;
      unaligned_mem_access = is_unaligned_mem_access();
      if (unaligned_mem_access) begin
        `uvm_info(`gfn, $sformatf("Unaligned: %0s, mem_addr:%0x", instr_name.name(), mem_addr),
                  UVM_HIGH)
      end
    end
    if (category == LOGICAL) begin
      logical_similarity = get_logical_similarity();
    end
    if (category == BRANCH) begin
      branch_hit = is_branch_hit();
    end
    if (instr_name inside {DIV, DIVU, REM, REMU, DIVW, DIVUW, REMW, REMUW}) begin
      div_result = get_div_result();
    end
  endfunction

  virtual function operand_sign_e get_operand_sign(bit [XLEN-1:0] value);
    if (value[XLEN-1]) begin
      return NEGATIVE;
    end else begin
      return POSITIVE;
    end
  endfunction

  virtual function bit is_unaligned_mem_access();
    if ((instr_name inside {LWU, LD, SD, C_LD, C_SD}) && (mem_addr % 8 != 0)) begin
      return 1'b1;
    end else if ((instr_name inside {LW, SW, C_LW, C_SW}) && (mem_addr % 4 != 0)) begin
      return 1'b1;
    end else if ((instr_name inside {LH, LHU, SH}) && (mem_addr % 2 != 0)) begin
      return 1'b1;
    end begin
      return 1'b0;
    end
  endfunction

  virtual function operand_sign_e get_imm_sign(bit [31:0] value);
    if (value[31]) begin
      return NEGATIVE;
    end else begin
      return POSITIVE;
    end
  endfunction

  virtual function div_result_e get_div_result();
    if (rs2_value == 0) begin
      return DIV_BY_ZERO;
    end else if ((rs2_value == '1) && (rs1_value == (1'b1 << (XLEN-1))))
      return DIV_OVERFLOW;
    else
      return DIV_NORMAL;
  endfunction

  virtual function special_val_e get_operand_special_val(bit [XLEN-1:0] value);
    if (value == 0) begin
      return ZERO_VAL;
    end else if (value == '1 << (XLEN-1)) begin
      return MIN_VAL;
    end else if (value == '1 >> 1) begin
      return MAX_VAL;
    end else begin
      return NORMAL_VAL;
    end
  endfunction

  virtual function special_val_e get_imm_special_val(bit [31:0] value);
    if (value == 0) begin
      return ZERO_VAL;
    end else if (format == U_FORMAT) begin
      // unsigend immediate value
      bit [31:0] max_val;
      max_val = (1 << imm_len)-1;
      if (value == max_val) begin
        return MAX_VAL;
      end
    end else begin
      // signed immediate value
      int signed max_val, min_val;
      max_val =  2 ** (imm_len-1) - 1;
      min_val = -2 ** (imm_len-1);
      if (min_val == $signed(value)) begin
        return MIN_VAL;
      end
      if (max_val == $signed(value)) begin
        return MAX_VAL;
      end
    end
    return NORMAL_VAL;
  endfunction

  virtual function compare_result_e get_compare_result();
    bit [XLEN-1:0] val1, val2;
    val1 = rs1_value;
    val2 = (format == I_FORMAT) ? imm : rs2_value;
    if (val1 == val2) begin
      return EQUAL;
    end else if (val1 < val2) begin
      return SMALLER;
    end else begin
      return LARGER;
    end
  endfunction

  virtual function bit is_branch_hit();
    case(instr_name)
      BEQ    : is_branch_hit = (rs1_value == rs2_value);
      C_BEQZ : is_branch_hit = (rs1_value == 0);
      BNE    : is_branch_hit = (rs1_value != rs2_value);
      C_BNEZ : is_branch_hit = (rs1_value != 0);
      BLT    : is_branch_hit = ($signed(rs1_value) <  $signed(rs2_value));
      BGE    : is_branch_hit = ($signed(rs1_value) >=  $signed(rs2_value));
      BLTU   : is_branch_hit = (rs1_value < rs2_value);
      BGEU   : is_branch_hit = (rs1_value >= rs2_value);
      default: `uvm_error(get_name(), $sformatf("Unexpected instr %0s", instr_name.name()))
    endcase
    return is_branch_hit;
  endfunction

  virtual function logical_similarity_e get_logical_similarity();
    bit [XLEN-1:0] val1, val2;
    int bit_difference;
    val1 = rs1_value;
    val2 = (format == I_FORMAT) ? imm : rs2_value;
    bit_difference = $countones(val1 ^ val2);
    if (val1 == val2)
      return IDENTICAL;
    else if (bit_difference == 32)
      return OPPOSITE;
    else if (bit_difference < 5)
      return SIMILAR;
    else
      return DIFFERENT;
  endfunction

  virtual function void check_hazard_condition(riscv_instr pre_instr);
    riscv_reg_t gpr;
    if (pre_instr.has_rd) begin
      if ((has_rs1 && (rs1 == pre_instr.rd)) || (has_rs2 && (rs2 == pre_instr.rd))) begin
        gpr_hazard = RAW_HAZARD;
      end else if (has_rd && (rd == pre_instr.rd)) begin
        gpr_hazard = WAW_HAZARD;
      end else if (has_rd && ((pre_instr.has_rs1 && (pre_instr.rs1 == rd)) ||
                              (pre_instr.has_rs2 && (pre_instr.rs2 == rd)))) begin
        gpr_hazard = WAR_HAZARD;
      end else begin
        gpr_hazard = NO_HAZARD;
      end
    end
    if (category == LOAD) begin
      if ((pre_instr.category == STORE) && (pre_instr.mem_addr == mem_addr)) begin
        lsu_hazard = RAW_HAZARD;
      end else begin
        lsu_hazard = NO_HAZARD;
      end
    end
    if (category == STORE) begin
      if ((pre_instr.category == STORE) && (pre_instr.mem_addr == mem_addr)) begin
        lsu_hazard = WAW_HAZARD;
      end else if ((pre_instr.category == LOAD) && (pre_instr.mem_addr == mem_addr)) begin
        lsu_hazard = WAR_HAZARD;
      end else begin
        lsu_hazard = NO_HAZARD;
      end
    end
    `uvm_info(`gfn, $sformatf("Pre:%0s, Cur:%0s, Hazard: %0s/%0s",
                              pre_instr.convert2asm(), this.convert2asm(),
                              gpr_hazard.name(), lsu_hazard.name()), UVM_FULL)
  endfunction

  virtual function void update_src_regs(string operands[$]);
    privileged_reg_t preg;
    case(format)
      J_FORMAT, U_FORMAT : begin
        // instr rd,imm
        `DV_CHECK_FATAL(operands.size() == 2)
        get_val(operands[1], imm);
      end
      I_FORMAT: begin
        `DV_CHECK_FATAL(operands.size() == 3, instr_name)
        if(category == LOAD) begin
          // load rd, imm(rs1) -> rd,rs1,imm
          rs1 = get_gpr(operands[1]);
          rs1_value = get_gpr_state(operands[1]);
          get_val(operands[2], imm);
        end else if(category == CSR) begin
          // csrrwi rd, csr, imm
          get_val(operands[2], imm);
          if (preg_enum::from_name(operands[1].toupper(), preg)) begin
            csr = preg;
          end else begin
            get_val(operands[1], csr);
          end
        end else begin
          // addi rd, rs1, imm
          rs1 = get_gpr(operands[1]);
          rs1_value = get_gpr_state(operands[1]);
          get_val(operands[2], imm);
        end
      end
      S_FORMAT, B_FORMAT: begin
        `DV_CHECK_FATAL(operands.size() == 3)
        if(category == STORE) begin
          // store rs2, imm(rs1) -> rs1,rs2,imm
          rs2 = get_gpr(operands[1]);
          rs2_value = get_gpr_state(operands[1]);
          rs1 = get_gpr(operands[0]);
          rs1_value = get_gpr_state(operands[0]);
          get_val(operands[2], imm);
        end else begin
          // bne rs1, rs2, imm
          rs1 = get_gpr(operands[0]);
          rs1_value = get_gpr_state(operands[0]);
          rs2 = get_gpr(operands[1]);
          rs2_value = get_gpr_state(operands[1]);
          get_val(operands[2], imm);
        end
      end
      R_FORMAT: begin
        if (has_rs2 || category == CSR) begin
          `DV_CHECK_FATAL(operands.size() == 3)
        end else begin
          `DV_CHECK_FATAL(operands.size() == 2)
        end
        if(category == CSR) begin
          // csrrw rd, csr, rs1
          if (preg_enum::from_name(operands[1].toupper(), preg)) begin
            csr = preg;
          end else begin
            get_val(operands[1], csr);
          end
          rs1 = get_gpr(operands[2]);
          rs1_value = get_gpr_state(operands[2]);
        end
        else begin
          // add rd, rs1, rs2
          rs1 = get_gpr(operands[1]);
          rs1_value = get_gpr_state(operands[1]);
          if (has_rs2) begin
            rs2 = get_gpr(operands[2]);
            rs2_value = get_gpr_state(operands[2]);
          end
        end
      end
      R4_FORMAT: begin
        `DV_CHECK_FATAL(operands.size() == 4)
        rs1 = get_gpr(operands[1]);
        rs1_value = get_gpr_state(operands[1]);
        rs2 = get_gpr(operands[2]);
        rs2_value = get_gpr_state(operands[2]);
        rs2 = get_gpr(operands[3]);
        rs2_value = get_gpr_state(operands[3]);
      end
      CI_FORMAT, CIW_FORMAT: begin
        if (instr_name == C_ADDI16SP) begin
          get_val(operands[1], imm);
          rs1 = SP;
          rs1_value = get_gpr_state("sp");
        end else if (instr_name == C_ADDI4SPN) begin
          rs1 = SP;
          rs1_value = get_gpr_state("sp");
        end else if (instr_name inside {C_LDSP, C_LWSP, C_LQSP}) begin
          // c.ldsp rd, imm
          get_val(operands[1], imm);
          rs1 = SP;
          rs1_value = get_gpr_state("sp");
        end else begin
          // c.lui rd, imm
          get_val(operands[1], imm);
        end
      end
      CL_FORMAT: begin
        // c.lw rd, imm(rs1) -> rd,rs1,imm
        get_val(operands[2], imm);
        rs1 = get_gpr(operands[1]);
        rs1_value = get_gpr_state(operands[1]);
      end
      CS_FORMAT: begin
        // c.sw rs2,imm(rs1) -> rs1,rs2,imm
        rs2 = get_gpr(operands[1]);
        rs2_value = get_gpr_state(operands[1]);
        rs1 = get_gpr(operands[0]);
        rs1_value = get_gpr_state(operands[0]);
        get_val(operands[2], imm);
      end
      CA_FORMAT: begin
        // c.and rd, rs2 (rs1 == rd)
        rs2 = get_gpr(operands[1]);
        rs2_value = get_gpr_state(operands[1]);
        rs1 = get_gpr(operands[0]);
        rs1_value = get_gpr_state(operands[0]);
      end
      CB_FORMAT: begin
        // c.beqz rs1, imm
        rs1 = get_gpr(operands[0]);
        rs1_value = get_gpr_state(operands[0]);
        get_val(operands[1], imm);
      end
      CSS_FORMAT: begin
        // c.swsp rs2, imm
        rs2 = get_gpr(operands[0]);
        rs2_value = get_gpr_state(operands[0]);
        rs1 = SP;
        rs1_value = get_gpr_state("sp");
        get_val(operands[1], imm);
      end
      CR_FORMAT: begin
        if (instr_name inside {C_JR, C_JALR}) begin
          // c.jalr rs1
          rs1 = get_gpr(operands[0]);
          rs1_value = get_gpr_state(operands[0]);
        end else begin
          // c.add rd, rs2
          rs2 = get_gpr(operands[1]);
          rs2_value = get_gpr_state(operands[1]);
        end
      end
      CJ_FORMAT: begin
        // c.j imm
        get_val(operands[0], imm);
      end
      default: `uvm_fatal(`gfn, $sformatf("Unsupported format %0s", format))
    endcase
  endfunction : update_src_regs

  virtual function void update_dst_regs(string reg_name, string val_str);
    get_val(val_str, gpr_state[reg_name], .hex(1));
    rd = get_gpr(reg_name);
    rd_value = get_gpr_state(reg_name);
  endfunction : update_dst_regs

  function riscv_reg_t get_gpr(input string str);
    str = str.toupper();
    if (!gpr_enum::from_name(str, get_gpr)) begin
      `uvm_fatal(`gfn, $sformatf("Cannot convert %0s to GPR", str))
    end
  endfunction : get_gpr

  virtual function bit [XLEN-1:0] get_gpr_state(string name);
    if (name inside {"zero", "x0"}) begin
      return 0;
    end else if (gpr_state.exists(name)) begin
      return gpr_state[name];
    end else begin
      `uvm_warning(`gfn, $sformatf("Cannot find GPR state: %0s", name))
      return 0;
    end
  endfunction : get_gpr_state
