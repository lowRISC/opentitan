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
  int unsigned              illegal_instr_cnt;

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
    cfg.build_instruction_template(.skip_instr_exclusion(1));
    instr = riscv_instr_cov_item::type_id::create("instr");
    instr.rand_mode(0);
    instr.no_hint_illegal_instr_c.constraint_mode(0);
    instr.imm_val_c.constraint_mode(0);
    instr_cg = new(cfg);
    `uvm_info(`gfn, $sformatf("%0d CSV trace files to be processed", trace_csv.size()), UVM_LOW)
    foreach (trace_csv[i]) begin
      entry_cnt = 0;
      instr_cg.reset();
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
            foreach (header[j]) begin
              trace[header[j]] = entry[j];
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
             `uvm_info(`gfn, $sformatf("Skipping illegal instr name: %0s [%0s]",
                             trace["instr"], line), UVM_LOW)
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
    if ((skipped_cnt > 0) || (illegal_instr_cnt > 0)) begin
      `uvm_error(`gfn, $sformatf("%0d instructions skipped, %0d illegal instruction",
                       skipped_cnt, illegal_instr_cnt))

    end else begin
      `uvm_info(`gfn, "TEST PASSED", UVM_NONE);
    end
  endtask

  virtual function void post_process_trace();
  endfunction

  function bit sample();
    riscv_instr_name_t instr_name;
    if (instr_enum::from_name(process_instr_name(trace["instr"]), instr_name)) begin
      if (cfg.instr_template.exists(instr_name)) begin
        instr.copy_base_instr(cfg.instr_template[instr_name]);
        assign_trace_info_to_instr(instr);
        instr.pre_sample();
        instr_cg.sample(instr);
        return 1'b1;
      end
    end
    illegal_instr_cnt++;
    return 1'b0;
  endfunction

  virtual function void assign_trace_info_to_instr(riscv_instr_cov_item instr);
    riscv_reg_t gpr;
    privileged_reg_t preg;
    get_val(trace["addr"], instr.pc);
    get_val(trace["binary"], instr.binary);
    instr.trace = trace["instr_str"];
    if (instr.instr_name inside {ECALL, EBREAK, FENCE, FENCE_I, NOP,
                                 C_NOP, WFI, MRET, C_EBREAK}) begin
      return;
    end
    if (instr.has_rs2) begin
      if (get_gpr(trace["rs2"], gpr)) begin
        instr.rs2 = gpr;
        get_val(trace["rs2_val"], instr.rs2_value);
      end else begin
        `uvm_error(`gfn, $sformatf("Unrecoganized rs2: [%0s] (%0s)",
                                   trace["rs2"], trace["csv_entry"]))
      end
    end
    if (instr.has_rd) begin
      if (get_gpr(trace["rd"], gpr)) begin
        instr.rd = gpr;
        get_val(trace["rd_val"], instr.rd_value);
      end else begin
        `uvm_error(`gfn, $sformatf("Unrecoganized rd: [%0s] (%0s)",
                                   trace["rd"], trace["csv_entry"]))
      end
    end
    if (instr.has_rs1) begin
      if (instr.format inside {CI_FORMAT, CR_FORMAT, CB_FORMAT}) begin
        instr.rs1 = instr.rd;
      end else begin
        if (get_gpr(trace["rs1"], gpr)) begin
          instr.rs1 = gpr;
          get_val(trace["rs1_val"], instr.rs1_value);
        end else begin
          `uvm_error(`gfn, $sformatf("Unrecoganized rs1: [%0s] (%0s)",
                                     trace["rs1"], trace["csv_entry"]))
        end
      end
    end
    if (instr.has_imm) begin
      get_val(trace["imm"], instr.imm);
    end
    if (instr.category == CSR) begin
      if (preg_enum::from_name(trace["csr"].toupper(), preg)) begin
        instr.csr = preg;
      end else begin
        get_val(trace["csr"], instr.csr);
      end
    end
    if (instr.category inside {LOAD, STORE}) begin
      if (XLEN == 32) begin
        instr.mem_addr = instr.rs1_value + instr.imm;
      end else begin
        bit [XLEN-32-1:0] padding;
        if (instr.imm[31]) begin
          padding = '1;
        end else begin
          padding = '0;
        end
        instr.mem_addr = instr.rs1_value + {padding, instr.imm};
      end
    end
  endfunction

  function bit get_gpr(input string str, output riscv_reg_t gpr);
    str = str.toupper();
    if (gpr_enum::from_name(str, gpr)) begin
      return 1'b1;
    end else begin
      return 1'b0;
    end
  endfunction

  function void get_val(input string str, output bit [XLEN-1:0] val);
    val = str.atohex();
  endfunction

  function string process_instr_name(string instr_name);
    instr_name = instr_name.toupper();
    foreach (instr_name[i]) begin
      if (instr_name[i] == ".") begin
        instr_name[i] = "_";
      end
    end
    return instr_name;
  endfunction

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
  endfunction

endclass
