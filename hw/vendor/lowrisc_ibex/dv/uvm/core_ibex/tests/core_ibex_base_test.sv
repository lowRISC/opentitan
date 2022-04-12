// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class core_ibex_base_test extends uvm_test;

  core_ibex_env                                   env;
  core_ibex_env_cfg                               cfg;
`ifdef INC_IBEX_COSIM
  core_ibex_cosim_cfg                             cosim_cfg;
`endif
  virtual clk_rst_if                              clk_vif;
  virtual core_ibex_dut_probe_if                  dut_vif;
  virtual core_ibex_instr_monitor_if              instr_vif;
  virtual core_ibex_csr_if                        csr_vif;
  mem_model_pkg::mem_model                        mem;
  core_ibex_vseq                                  vseq;
  bit                                             enable_irq_seq;
  int unsigned                                    timeout_in_cycles = 100000000;
  int unsigned                                    max_quit_count  = 1;
  // If no signature_addr handshake functionality is desired between the testbench and the generated
  // code, the test will wait for the specifield number of cycles before starting stimulus
  // sequences (irq and debug)
  int unsigned                                    stimulus_delay = 800;
  bit[ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0]    signature_data_q[$];
  bit[ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0]    signature_data;
  uvm_tlm_analysis_fifo #(ibex_mem_intf_seq_item) item_collected_port;
  uvm_tlm_analysis_fifo #(irq_seq_item)           irq_collected_port;
  uvm_phase                                       cur_run_phase;

  `uvm_component_utils(core_ibex_base_test)

  function new(string name="", uvm_component parent=null);
    core_ibex_report_server ibex_report_server;
    super.new(name, parent);
    ibex_report_server = new();
    uvm_report_server::set_server(ibex_report_server);
    item_collected_port = new("item_collected_port_test", this);
    irq_collected_port  = new("irq_collected_port_test", this);
  endfunction

  function string get_isa_string();
    bit     RV32E;
    rv32m_e RV32M;
    rv32b_e RV32B;
    string  isa;

    if (!uvm_config_db#(bit)::get(null, "", "RV32E", RV32E)) begin
      `uvm_fatal(`gfn, "Cannot get RV32E parameter")
    end
    if (!uvm_config_db#(rv32m_e)::get(null, "", "RV32M", RV32M)) begin
      `uvm_fatal(`gfn, "Cannot get RV32M parameter")
    end
    if (!uvm_config_db#(rv32b_e)::get(null, "", "RV32B", RV32B)) begin
      `uvm_fatal(`gfn, "Cannot get RV32B parameter")
    end

    // Construct the right ISA string for the cosimulator by looking at top-level testbench
    // parameters.
    //
    // Note that the bitmanip extensions from the v0.93 spec (Zbe, Zbf, Zbp, Zbr, Zbt) are all
    // contained in "Xbitmanip" for Spike at the moment. The specific parts used are listed in
    // comments below.
    isa = {"rv32", RV32E ? "e" : "i"};
    if (RV32M != RV32MNone) isa = {isa, "m"};
    isa = {isa, "c"};
    case (RV32B)
      RV32BNone:
        ;
      RV32BBalanced:
        isa = {isa, "_Zba_Zbb_Zbs_Xbitmanip"}; // + Zbf, Zbt
      RV32BOTEarlGrey:
        isa = {isa, "_Zba_Zbb_Zbc_Zbs_Xbitmanip"}; // + Zbf, Zbp, Zbr, Zbt
      RV32BFull:
        isa = {isa, "_Zba_Zbb_Zbc_Zbs_Xbitmanip"}; // + Zbe, Zbf, Zbp, Zbr, Zbt
    endcase

    return isa;
  endfunction

  virtual function void build_phase(uvm_phase phase);
    string cosim_log_file;

    super.build_phase(phase);
    $value$plusargs("timeout_in_cycles=%0d", timeout_in_cycles);
    if (!uvm_config_db#(virtual clk_rst_if)::get(null, "", "clk_if", clk_vif)) begin
      `uvm_fatal(`gfn, "Cannot get clk_if")
    end
    if (!uvm_config_db#(virtual core_ibex_dut_probe_if)::get(null, "", "dut_if", dut_vif)) begin
      `uvm_fatal(`gfn, "Cannot get dut_if")
    end
    if (!uvm_config_db#(virtual core_ibex_instr_monitor_if)::get(null, "",
                                                                 "instr_monitor_if",
                                                                 instr_vif)) begin
      `uvm_fatal(`gfn, "Cannot get instr_monitor_if")
    end
    if (!uvm_config_db#(virtual core_ibex_csr_if)::get(null, "", "csr_if", csr_vif)) begin
      `uvm_fatal(`gfn, "Cannot get csr_if")
    end
    env = core_ibex_env::type_id::create("env", this);
    cfg = core_ibex_env_cfg::type_id::create("cfg", this);

`ifdef INC_IBEX_COSIM
    cosim_cfg = core_ibex_cosim_cfg::type_id::create("cosim_cfg", this);

    cosim_cfg.isa_string = get_isa_string();
    cosim_cfg.start_pc = {{32'h`BOOT_ADDR}[31:8], 8'h80};
    cosim_cfg.start_mtvec = {{32'h`BOOT_ADDR}[31:8], 8'h1};
    // TODO: Turn on when not using icache
    cosim_cfg.probe_imem_for_errs = 1'b0;
    void'($value$plusargs("cosim_log_file=%0s", cosim_log_file));
    cosim_cfg.log_file = cosim_log_file;

    uvm_config_db#(core_ibex_cosim_cfg)::set(null, "*cosim_agent*", "cosim_cfg", cosim_cfg);
`endif

    uvm_config_db#(core_ibex_env_cfg)::set(this, "*", "cfg", cfg);
    mem = mem_model_pkg::mem_model#()::type_id::create("mem");
    // Create virtual sequence and assign memory handle
    vseq = core_ibex_vseq::type_id::create("vseq");
    vseq.mem = mem;
    vseq.cfg = cfg;
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    env.data_if_response_agent.monitor.item_collected_port.connect(
      this.item_collected_port.analysis_export);
    env.irq_agent.monitor.irq_port.connect(this.irq_collected_port.analysis_export);
  endfunction

  virtual task run_phase(uvm_phase phase);
    enable_irq_seq = cfg.enable_irq_single_seq || cfg.enable_irq_multiple_seq;
    phase.raise_objection(this);
    cur_run_phase = phase;
    dut_vif.dut_cb.fetch_enable <= ibex_pkg::FetchEnableOff;
    clk_vif.wait_clks(100);
    load_binary_to_mem();
    dut_vif.dut_cb.fetch_enable <= ibex_pkg::FetchEnableOn;
    send_stimulus();
    wait_for_test_done();
    cur_run_phase = null;
    phase.drop_objection(this);
  endtask

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    void'($value$plusargs("max_quit_count=%0d", max_quit_count));
    uvm_report_server::get_server().set_max_quit_count(max_quit_count);
  endfunction

  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
  endfunction

  virtual task send_stimulus();
    vseq.start(env.vseqr);
  endtask

  virtual task check_perf_stats();
  endtask

  function void load_binary_to_mem();
    string      bin;
    bit [7:0]   r8;
    bit [31:0]  addr = 32'h`BOOT_ADDR;
    int         f_bin;
    void'($value$plusargs("bin=%0s", bin));
    if (bin == "")
      `uvm_fatal(get_full_name(), "Please specify test binary by +bin=binary_name")
    `uvm_info(get_full_name(), $sformatf("Running test : %0s", bin), UVM_LOW)
    f_bin = $fopen(bin,"rb");
    if (!f_bin)
      `uvm_fatal(get_full_name(), $sformatf("Cannot open file %0s", bin))
    while ($fread(r8,f_bin)) begin
      `uvm_info(`gfn, $sformatf("Init mem [0x%h] = 0x%0h", addr, r8), UVM_FULL)
      mem.write(addr, r8);
`ifdef INC_IBEX_COSIM
      if (env.cosim_agent != null) begin
        env.cosim_agent.write_mem_byte(addr, r8);
      end
`endif
      addr++;
    end
  endfunction

  virtual task wait_for_test_done();
    fork
      begin
        wait (dut_vif.ecall === 1'b1);
        vseq.stop();
        `uvm_info(`gfn, "ECALL instruction is detected, test done", UVM_LOW)
        fork
          begin
            check_perf_stats();
            // De-assert fetch enable to finish the test
            clk_vif.wait_clks(10);
            dut_vif.dut_cb.fetch_enable <= ibex_pkg::FetchEnableOff;
          end
          // Wait some time for the remaining instruction to finish
          clk_vif.wait_clks(3000);
        join
      end
      begin
        clk_vif.wait_clks(timeout_in_cycles);
        `uvm_fatal(`gfn, "TEST TIMEOUT!!")
      end
    join_any
  endtask


  virtual task wait_for_mem_txn(input bit[ibex_mem_intf_agent_pkg::ADDR_WIDTH-1:0] ref_addr,
                                input signature_type_t ref_type);
    ibex_mem_intf_seq_item mem_txn;
    forever begin
      // The first write to this address is guaranteed to contain the signature type in bits [7:0]
      item_collected_port.get(mem_txn);
      if (mem_txn.addr == ref_addr && mem_txn.data[7:0] === ref_type &&
          mem_txn.read_write == WRITE) begin
        signature_data = mem_txn.data;
        case (ref_type)
          // The very first write to the signature address in every test is guaranteed to be a write
          // of CORE_STATUS, indicating the INITIALIZED state
          CORE_STATUS: begin
            signature_data_q.push_back(signature_data >> 8);
          end
          TEST_RESULT: begin
            signature_data_q.push_back(signature_data >> 8);
          end
          // The next 32 writes to the address are guaranteed to be a dump of all GPRs
          WRITE_GPR: begin
            for(int i = 0; i < 32; i++) begin
              do begin
                item_collected_port.get(mem_txn);
              end while(!(mem_txn.addr == ref_addr && mem_txn.read_write == WRITE));
              signature_data_q.push_back(mem_txn.data);
            end
          end
          // The next write to this address is guaranteed to be the data held in the CSR
          WRITE_CSR: begin
            signature_data_q.push_back(signature_data >> 8);
            do begin
              item_collected_port.get(mem_txn);
            end while (!(mem_txn.addr == ref_addr && mem_txn.read_write == WRITE));
            signature_data_q.push_back(mem_txn.data);
          end
          default: begin
            `uvm_fatal(`gfn,
              $sformatf("The data 0x%0h written to the signature address is formatted incorrectly.",
                        signature_data))
          end
        endcase
        return;
      end
    end
  endtask

  // API of various tasks wrapping wait_for_mem_txn, for various common functionalities that
  // might be needed for verification purposes.
  // Will be expanded as needed.

  // Gets the next CORE_STATUS signature write and compares it against the provided core_status
  // type, throws uvm_error on mismatch
  virtual task check_next_core_status(core_status_t core_status, string error_msg = "",
                                      int timeout = 9999999);
    cur_run_phase.raise_objection(this);
    fork
      begin
        wait_for_mem_txn(cfg.signature_addr, CORE_STATUS);
        signature_data = signature_data_q.pop_front();
        `DV_CHECK_EQ_FATAL(signature_data, core_status, error_msg);
      end
      begin : wait_timeout
        clk_vif.wait_clks(timeout);
        `uvm_fatal(`gfn,
                   $sformatf("Did not receive core_status %0s within %0d cycle timeout period",
                   core_status.name(), timeout))
      end
    join_any
    // Will only get here if we successfully beat the timeout period
    disable fork;
    cur_run_phase.drop_objection(this);
  endtask

  // Waits for a write to the address of the specified CSR and retrieves the csr data
  virtual task wait_for_csr_write(csr_num_e csr, int timeout = 9999999);
    bit [11:0] csr_addr;
    cur_run_phase.raise_objection(this);
    fork
      begin
        do begin
          wait_for_mem_txn(cfg.signature_addr, WRITE_CSR);
          csr_addr = signature_data_q.pop_front();
          signature_data = signature_data_q.pop_front();
        end while (csr_addr != csr);
      end
      begin : wait_timeout
        clk_vif.wait_clks(timeout);
        `uvm_fatal(`gfn,
                   $sformatf("Did not receive write to csr 0x%0x within %0d cycle timeout period",
                   csr, timeout))
      end
    join_any
    // Will only get here if we successfully beat the timeout period
    disable fork;
    cur_run_phase.drop_objection(this);
  endtask

  // Waits until the next time the given core_status is written to the signature address
  virtual task wait_for_core_status(core_status_t core_status);
    do begin
      wait_for_mem_txn(cfg.signature_addr, CORE_STATUS);
      signature_data = signature_data_q.pop_front();
    end while (signature_data != core_status);
  endtask

endclass
