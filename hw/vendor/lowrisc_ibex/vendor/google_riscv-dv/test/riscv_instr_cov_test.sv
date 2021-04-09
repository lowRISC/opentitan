// This test read all trace CSV, and collect functional coverage from the instruction trace
class riscv_instr_cov_test extends uvm_test;

  typedef uvm_enum_wrapper#(riscv_instr_name_t) instr_enum;

  riscv_instr_gen_config    cfg;
  riscv_instr_cover_group   instr_cg;
  string                    trace_csv[$];
  string                    trace[string];
  bit                       report_illegal_instr;
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
    void'($value$plusargs("report_illegal_instr=%0d", report_illegal_instr));
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
    riscv_instr::create_instr_list(cfg);
    instr_cg = new(cfg);
    `uvm_info(`gfn, $sformatf("%0d CSV trace files to be processed", trace_csv.size()), UVM_LOW)
    foreach (trace_csv[i]) begin
      bit expect_illegal_instr;
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
              if (report_illegal_instr) begin
               `uvm_error(`gfn, $sformatf("Found unexpected illegal instr: %0s [%0s]",
                                          trace["instr"], line))
              end
              illegal_instr_cnt++;
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
    if ((skipped_cnt > 0) || ((illegal_instr_cnt > 0) && report_illegal_instr)) begin
      `uvm_error(`gfn, $sformatf("%0d instructions skipped, %0d illegal instruction",
                       skipped_cnt, illegal_instr_cnt))

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
      if (riscv_instr::instr_template.exists(instr_name)) begin
        riscv_instr instr;
        instr = riscv_instr::get_instr(instr_name);
        if ((instr.group inside {RV32I, RV32M, RV32C, RV64I, RV64M, RV64C,
                                 RV32F, RV64F, RV32D, RV64D, RV32B, RV64B}) &&
            (instr.group inside {supported_isa})) begin
          assign_trace_info_to_instr(instr);
          instr.pre_sample();
          instr_cg.sample(instr);
        end
        return 1'b1;
      end
    end
    `uvm_info(`gfn, $sformatf("Cannot find opcode: %0s",
                              process_instr_name(trace["instr"])), UVM_LOW)
  endfunction

  virtual function void assign_trace_info_to_instr(riscv_instr instr);
    riscv_reg_t gpr;
    string operands[$];
    string gpr_update[$];
    string pair[$];
    get_val(trace["pc"], instr.pc, .hex(1));
    get_val(trace["binary"], instr.binary, .hex(1));
    instr.trace = trace["instr_str"];
    if (instr.instr_name inside {NOP, WFI, FENCE, FENCE_I, EBREAK, C_EBREAK, SFENCE_VMA,
                                 ECALL, C_NOP, MRET, SRET, URET}) begin
      return;
    end

    split_string(trace["operand"], ",", operands);
    instr.update_src_regs(operands);

    split_string(trace["gpr"], ";", gpr_update);
    foreach (gpr_update[i]) begin
      split_string(gpr_update[i], ":", pair);
      if (pair.size() != 2) begin
        `uvm_fatal(`gfn, $sformatf("Illegal gpr update format: %0s", gpr_update[i]))
      end
      instr.update_dst_regs(pair[0], pair[1]);
    end
  endfunction : assign_trace_info_to_instr

  function string process_instr_name(string instr_name);
    instr_name = instr_name.toupper();
    foreach (instr_name[i]) begin
      if (instr_name[i] == ".") begin
        instr_name[i] = "_";
      end
    end

    case (instr_name)
      // rename to new name as ovpsim still uses old name
     "FMV_S_X": instr_name = "FMV_W_X";
     "FMV_X_S": instr_name = "FMV_X_W";
      // convert Pseudoinstructions
      // fmv.s rd, rs fsgnj.s rd, rs, rs Copy single-precision register
      // fabs.s rd, rs fsgnjx.s rd, rs, rs Single-precision absolute value
      // fneg.s rd, rs fsgnjn.s rd, rs, rs Single-precision negate
      // fmv.d rd, rs fsgnj.d rd, rs, rs Copy double-precision register
      // fabs.d rd, rs fsgnjx.d rd, rs, rs Double-precision absolute value
      // fneg.d rd, rs fsgnjn.d rd, rs, rs Double-precision negate
      "FMV_S":  instr_name = "FSGNJ_S";
      "FABS_S": instr_name = "FSGNJX_S";
      "FNEG_S": instr_name = "FSGNJN_S";
      "FMV_D":  instr_name = "FSGNJ_D";
      "FABS_D": instr_name = "FSGNJX_D";
      "FNEG_D": instr_name = "FSGNJN_D";
      default: ;
    endcase

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
