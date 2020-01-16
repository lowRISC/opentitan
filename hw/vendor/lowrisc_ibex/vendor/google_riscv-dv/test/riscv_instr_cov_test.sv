// This test read all trace CSV, and collect functional coverage from the instruction trace
class riscv_instr_cov_test extends uvm_test;

  typedef uvm_enum_wrapper#(riscv_instr_name_t) instr_enum;
  typedef uvm_enum_wrapper#(riscv_reg_t) gpr_enum;
  typedef uvm_enum_wrapper#(privileged_reg_t) preg_enum;

  riscv_instr_gen_config    cfg;
  riscv_instr_cover_group   instr_cg;
  riscv_instr_cov_item      instr;
  string                    trace_csv[$];
  string                    trace[string];
  int unsigned              entry_cnt;
  int unsigned              total_entry_cnt;
  int unsigned              skipped_cnt;
  int unsigned              unexpected_illegal_instr_cnt;
  bit [XLEN-1:0]            gpr_state[string];

  `uvm_component_utils(riscv_instr_cov_test)
  `uvm_component_new

  task run_phase(uvm_phase phase);
    int i;
    string args;
    string csv;
    string line;
    string header[$];
    string entry[$];
    int fd;
    while(1) begin
      args = {$sformatf("trace_csv_%0d", i), "=%s"};
      if ($value$plusargs(args, csv)) begin
        trace_csv.push_back(csv);
      end else begin
        break;
      end
      i++;
    end
    cfg = riscv_instr_gen_config::type_id::create("cfg");
    // disable_compressed_instr is not relevant to coverage test
    cfg.disable_compressed_instr = 0;
    `ifdef DEPRECATED
      cfg.build_instruction_template(.skip_instr_exclusion(1));
    `else
      riscv_instr::create_instr_list(cfg);
    `endif
    instr = riscv_instr_cov_item::type_id::create("instr");
    instr.rand_mode(0);
    `ifdef DEPRECATED
    instr.no_hint_illegal_instr_c.constraint_mode(0);
    instr.imm_val_c.constraint_mode(0);
    `endif
    instr_cg = new(cfg);
    `uvm_info(`gfn, $sformatf("%0d CSV trace files to be processed", trace_csv.size()), UVM_LOW)
    foreach (trace_csv[i]) begin
      bit expect_illegal_instr;
      entry_cnt = 0;
      instr_cg.reset();
      if (uvm_is_match("*illegal*", trace_csv[i])) begin
        expect_illegal_instr = 1;
      end
      `uvm_info(`gfn, $sformatf("Processing CSV trace[%0d]: %s", i, trace_csv[i]), UVM_LOW)
      fd = $fopen(trace_csv[i], "r");
      if (fd) begin
        // Get the header line
        if ($fgets(line, fd)) begin
          split_string(line, ",", header);
          `uvm_info(`gfn, $sformatf("Header: %0s", line), UVM_HIGH);
        end else begin
          `uvm_info(`gfn, $sformatf("Skipping empty trace file: %0s", trace_csv[i]), UVM_LOW)
          continue;
        end
        while ($fgets(line, fd)) begin
          split_string(line, ",", entry);
          if (entry.size() != header.size()) begin
            `uvm_info(`gfn, $sformatf("Skipping malformed entry[%0d] : %0s", entry_cnt, line), UVM_LOW)
            skipped_cnt += 1;
          end else begin
            trace["csv_entry"] = line;
            `uvm_info("", "----------------------------------------------------------", UVM_HIGH)
            foreach (header[j]) begin
              trace[header[j]] = entry[j];
              if (header[j].substr(0,2) != "pad") begin
                `uvm_info("", $sformatf("%0s=%0s", header[j], entry[j]), UVM_HIGH)
              end
            end
            post_process_trace();
            if (trace["instr"] inside {"li", "ret", "la"}) continue;
            if (uvm_is_match("amo*",trace["instr"]) ||
                uvm_is_match("lr*" ,trace["instr"]) ||
                uvm_is_match("sc*" ,trace["instr"])) begin
              // TODO: Enable functional coverage for AMO test
              continue;
            end
            if (!sample()) begin
              if (!expect_illegal_instr) begin
               `uvm_error(`gfn, $sformatf("Found unexpected illegal instr: %0s [%0s]",
                                          trace["instr"], line))
                unexpected_illegal_instr_cnt++;
              end
            end
          end
          entry_cnt += 1;
        end
      end else begin
        `uvm_error(`gfn, $sformatf("%0s cannot be openned", trace_csv[i]))
      end
      `uvm_info(`gfn, $sformatf("[%s] : %0d instructions processed",
                      trace_csv[i], entry_cnt), UVM_LOW)
      total_entry_cnt += entry_cnt;
    end
    `uvm_info(`gfn, $sformatf("Finished processing %0d trace CSV, %0d instructions",
                     trace_csv.size(), total_entry_cnt), UVM_LOW)
    if ((skipped_cnt > 0) || (unexpected_illegal_instr_cnt > 0)) begin
      `uvm_error(`gfn, $sformatf("%0d instructions skipped, %0d illegal instruction",
                       skipped_cnt, unexpected_illegal_instr_cnt))

    end else begin
      `uvm_info(`gfn, "TEST PASSED", UVM_NONE);
    end
  endtask

  virtual function void post_process_trace();
  endfunction

  function void fatal (string str);
    `uvm_info(`gfn, str, UVM_NONE);
    if ($test$plusargs("stop_on_first_error")) begin
      `uvm_fatal(`gfn, "Errors: *. Warnings: * (written by riscv_instr_cov.sv)")
    end
  endfunction

  function bit sample();
    riscv_instr_name_t instr_name;
    bit [XLEN-1:0] binary;
    get_val(trace["binary"], binary, .hex(1));
    if ((binary[1:0] != 2'b11) && (RV32C inside {supported_isa})) begin
      `SAMPLE(instr_cg.compressed_opcode_cg, binary[15:0])
      `SAMPLE(instr_cg.illegal_compressed_instr_cg, binary)
    end
    if (binary[1:0] == 2'b11) begin
      `SAMPLE(instr_cg.opcode_cg, binary[6:2])
    end
    if (instr_enum::from_name(process_instr_name(trace["instr"]), instr_name)) begin
    `ifdef DEPRECATED
      if (cfg.instr_template.exists(instr_name)) begin
        instr.copy_base_instr(cfg.instr_template[instr_name]);
    `else
      if (riscv_instr::instr_template.exists(instr_name)) begin
        instr.copy(riscv_instr::instr_template[instr_name]);
    `endif
        if (instr.group inside {RV32I, RV32M, RV32C, RV64I, RV64M, RV64C}) begin
          assign_trace_info_to_instr(instr);
        end
        instr.pre_sample();
        instr_cg.sample(instr);
        return 1'b1;
      end
    end
    `uvm_info(`gfn, $sformatf("Cannot find opcode: %0s",
                              process_instr_name(trace["instr"])), UVM_LOW)
  endfunction

  virtual function void assign_trace_info_to_instr(riscv_instr_cov_item instr);
    riscv_reg_t gpr;
    string operands[$];
    string gpr_update[$];
    string pair[$];
    privileged_reg_t preg;
    get_val(trace["pc"], instr.pc, .hex(1));
    get_val(trace["binary"], instr.binary, .hex(1));
    instr.trace = trace["instr_str"];
    if (instr.instr_name inside {NOP, WFI, FENCE, FENCE_I, EBREAK, C_EBREAK, SFENCE_VMA,
                                 ECALL, C_NOP, MRET, SRET, URET}) begin
      return;
    end
    split_string(trace["operand"], ",", operands);
    case(instr.format)
      J_FORMAT, U_FORMAT : begin
        // instr rd,imm
        `DV_CHECK_FATAL(operands.size() == 2)
        get_val(operands[1], instr.imm);
      end
      I_FORMAT: begin
        `DV_CHECK_FATAL(operands.size() == 3, trace["instr_str"])
        if(instr.category == LOAD) begin
          // load rd, imm(rs1)
          instr.rs1 = get_gpr(operands[2]);
          instr.rs1_value = get_gpr_state(operands[2]);
          get_val(operands[1], instr.imm);
        end else if(instr.category == CSR) begin
          // csrrwi rd, csr, imm
          get_val(operands[2], instr.imm);
          if (preg_enum::from_name(operands[1].toupper(), preg)) begin
            instr.csr = preg;
          end else begin
            get_val(operands[1], instr.csr);
          end
        end else begin
          // addi rd, rs1, imm
          instr.rs1 = get_gpr(operands[1]);
          instr.rs1_value = get_gpr_state(operands[1]);
          get_val(operands[2], instr.imm);
        end
      end
      S_FORMAT, B_FORMAT: begin
        `DV_CHECK_FATAL(operands.size() == 3)
        if(instr.category == STORE) begin
          // sw rs2,imm(rs1)
          instr.rs2 = get_gpr(operands[0]);
          instr.rs2_value = get_gpr_state(operands[0]);
          instr.rs1 = get_gpr(operands[2]);
          instr.rs1_value = get_gpr_state(operands[2]);
          get_val(operands[1], instr.imm);
        end else begin
          // bne rs1, rs2, imm
          instr.rs1 = get_gpr(operands[0]);
          instr.rs1_value = get_gpr_state(operands[0]);
          instr.rs2 = get_gpr(operands[1]);
          instr.rs2_value = get_gpr_state(operands[1]);
          get_val(operands[2], instr.imm);
        end
      end
      R_FORMAT: begin
        `DV_CHECK_FATAL(operands.size() == 3)
        if(instr.category == CSR) begin
          // csrrw rd, csr, rs1
          if (preg_enum::from_name(operands[1].toupper(), preg)) begin
            instr.csr = preg;
          end else begin
            get_val(operands[1], instr.csr);
          end
          instr.rs1 = get_gpr(operands[2]);
          instr.rs1_value = get_gpr_state(operands[2]);
        end else begin
          // add rd, rs1, rs2
          instr.rs1 = get_gpr(operands[1]);
          instr.rs1_value = get_gpr_state(operands[1]);
          instr.rs2 = get_gpr(operands[2]);
          instr.rs2_value = get_gpr_state(operands[2]);
        end
      end
      CI_FORMAT, CIW_FORMAT: begin
        if (instr.instr_name == C_ADDI16SP) begin
          get_val(operands[1], instr.imm);
          instr.rs1 = SP;
          instr.rs1_value = get_gpr_state("sp");
        end else if (instr.instr_name == C_ADDI4SPN) begin
          instr.rs1 = SP;
          instr.rs1_value = get_gpr_state("sp");
        end else if (instr.instr_name inside {C_LDSP, C_LWSP, C_LQSP}) begin
          // c.ldsp rd, imm
          get_val(operands[1], instr.imm);
          instr.rs1 = SP;
          instr.rs1_value = get_gpr_state("sp");
        end else begin
          // c.lui rd, imm
          get_val(operands[1], instr.imm);
        end
      end
      CL_FORMAT: begin
        // c.lw rd, imm(rs1)
        get_val(operands[1], instr.imm);
        instr.rs1 = get_gpr(operands[2]);
        instr.rs1_value = get_gpr_state(operands[2]);
      end
      CS_FORMAT: begin
        // c.sw rs2,imm(rs1)
        instr.rs2 = get_gpr(operands[0]);
        instr.rs2_value = get_gpr_state(operands[0]);
        instr.rs1 = get_gpr(operands[2]);
        instr.rs1_value = get_gpr_state(operands[2]);
        get_val(operands[1], instr.imm);
      end
      CA_FORMAT: begin
        // c.and rd, rs2 (rs1 == rd)
        instr.rs2 = get_gpr(operands[1]);
        instr.rs2_value = get_gpr_state(operands[1]);
        instr.rs1 = get_gpr(operands[0]);
        instr.rs1_value = get_gpr_state(operands[0]);
      end
      CB_FORMAT: begin
        // c.beqz rs1, imm
        instr.rs1 = get_gpr(operands[0]);
        instr.rs1_value = get_gpr_state(operands[0]);
        get_val(operands[1], instr.imm);
      end
      CSS_FORMAT: begin
        // c.swsp rs2, imm
        instr.rs2 = get_gpr(operands[0]);
        instr.rs2_value = get_gpr_state(operands[0]);
        instr.rs1 = SP;
        instr.rs1_value = get_gpr_state("sp");
        get_val(operands[1], instr.imm);
      end
      CR_FORMAT: begin
        if (instr.instr_name inside {C_JR, C_JALR}) begin
          // c.jalr rs1
          instr.rs1 = get_gpr(operands[0]);
          instr.rs1_value = get_gpr_state(operands[0]);
        end else begin
          // c.add rd, rs2
          instr.rs2 = get_gpr(operands[1]);
          instr.rs2_value = get_gpr_state(operands[1]);
        end
      end
      CJ_FORMAT: begin
        // c.j imm
        get_val(operands[0], instr.imm);
      end
    endcase
    split_string(trace["gpr"], ";", gpr_update);
    foreach (gpr_update[i]) begin
      split_string(gpr_update[i], ":", pair);
      if (pair.size() != 2) begin
        `uvm_fatal(`gfn, $sformatf("Illegal gpr update format: %0s", gpr_update[i]))
      end
      get_val(pair[1], gpr_state[pair[0]], .hex(1));
      instr.rd = get_gpr(pair[0]);
      instr.rd_value = get_gpr_state(pair[0]);
    end
  endfunction : assign_trace_info_to_instr

  function riscv_reg_t get_gpr(input string str);
    str = str.toupper();
    if (!gpr_enum::from_name(str, get_gpr)) begin
      `uvm_fatal(`gfn, $sformatf("Cannot convert %0s to GPR", str))
    end
  endfunction : get_gpr

  function bit [XLEN-1:0] get_gpr_state(string name);
    if (name inside {"zero", "x0"}) begin
      return 0;
    end else if (gpr_state.exists(name)) begin
      return gpr_state[name];
    end else begin
      `uvm_warning(`gfn, $sformatf("Cannot find GPR state: %0s", name))
      return 0;
    end
  endfunction : get_gpr_state

  function void get_val(input string str, output bit [XLEN-1:0] val, input hex = 0);
    if (str.len() > 2) begin
      if (str.substr(0, 1) == "0x") begin
        str = str.substr(2, str.len() -1);
        val = str.atohex();
        return;
      end
    end
    if (hex) begin
      val = str.atohex();
    end else begin
      if (str.substr(0, 0) == "-") begin
        str = str.substr(1, str.len() - 1);
        val = -str.atoi();
      end else begin
        val = str.atoi();
      end
    end
    `uvm_info(`gfn, $sformatf("imm:%0s -> 0x%0x/%0d", str, val, $signed(val)), UVM_FULL)
  endfunction : get_val

  function string process_instr_name(string instr_name);
    instr_name = instr_name.toupper();
    foreach (instr_name[i]) begin
      if (instr_name[i] == ".") begin
        instr_name[i] = "_";
      end
    end
    return instr_name;
  endfunction : process_instr_name

  function void split_string(string str, byte step, ref string result[$]);
    string tmp_str;
    int i;
    bit in_quote;
    result = {};
    while (i < str.len()) begin
      if (str[i] == "\"") begin
        in_quote = ~in_quote;
      end else if ((str[i] == step) && !in_quote) begin
        result.push_back(tmp_str);
        tmp_str = "";
      end else begin
        tmp_str = {tmp_str, str[i]};
      end
      if (i == str.len()-1) begin
        result.push_back(tmp_str);
      end
      i++;
    end
  endfunction : split_string

  function void report_phase(uvm_phase phase);
    uvm_report_server rs;
    int error_count;
    rs = uvm_report_server::get_server();
    error_count = rs.get_severity_count(UVM_WARNING) +
                  rs.get_severity_count(UVM_ERROR) +
                  rs.get_severity_count(UVM_FATAL);
    if (error_count == 0) begin
      `uvm_info("", "TEST PASSED", UVM_NONE);
    end else begin
      `uvm_info("", "TEST FAILED", UVM_NONE);
    end
    `uvm_info("", "TEST GENERATION DONE", UVM_NONE);
    super.report_phase(phase);
  endfunction : report_phase

endclass
