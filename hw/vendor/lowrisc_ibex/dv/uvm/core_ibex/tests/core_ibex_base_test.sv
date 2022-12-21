// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "date_dpi.svh"

class core_ibex_base_test extends uvm_test;

  core_ibex_env                                   env;
  core_ibex_env_cfg                               cfg;
  core_ibex_cosim_cfg                             cosim_cfg;
  ibex_mem_intf_response_agent_cfg                imem_cfg;
  ibex_mem_intf_response_agent_cfg                dmem_cfg;
  virtual clk_rst_if                              clk_vif;
  virtual core_ibex_dut_probe_if                  dut_vif;
  virtual core_ibex_instr_monitor_if              instr_vif;
  virtual core_ibex_csr_if                        csr_vif;
  mem_model_pkg::mem_model                        mem;
  core_ibex_vseq                                  vseq;
  string                                          binary;
  bit                                             enable_irq_seq;
  longint                                         timeout_seconds = 1800; // wall-clock seconds
  int unsigned                                    timeout_in_cycles = 100000000;
  int unsigned                                    max_quit_count  = 1;
  // If no signature_addr handshake functionality is desired between the testbench and the generated
  // code, the test will wait for the specifield number of cycles before starting stimulus
  // sequences (irq and debug)
  int unsigned                                    stimulus_delay = 800;
  bit[ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0]    signature_data_q[$];
  bit[ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0]    signature_data;
  uvm_tlm_analysis_fifo #(ibex_mem_intf_seq_item) item_collected_port;
  uvm_tlm_analysis_fifo #(ibex_mem_intf_seq_item) test_done_port;
  uvm_tlm_analysis_fifo #(irq_seq_item)           irq_collected_port;
  uvm_phase                                       cur_run_phase;
  bit                                             test_done = 1'b0;

  `uvm_component_utils(core_ibex_base_test)

  function new(string name="", uvm_component parent=null);
    core_ibex_report_server ibex_report_server;
    super.new(name, parent);
    ibex_report_server = new();
    uvm_report_server::set_server(ibex_report_server);
    item_collected_port = new("item_collected_port_test", this);
    test_done_port = new("test_done_port_instance", this);
    irq_collected_port  = new("irq_collected_port_test", this);
  endfunction

  // NOTE: This logic should match the code in the get_isas_for_config() function in
  //       core_ibex/scripts/scripts_lib.py: keep them in sync!
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
    isa = {"rv32", RV32E ? "e" : "i"};
    if (RV32M != RV32MNone) isa = {isa, "m"};
    isa = {isa, "c"};
    case (RV32B)
      RV32BNone:
        ;
      RV32BBalanced:
        isa = {isa, "_Zba_Zbb_Zbs_XZbf_XZbt"};
      RV32BOTEarlGrey:
        isa = {isa, "_Zba_Zbb_Zbc_Zbs_XZbf_XZbp_XZbr_XZbt"};
      RV32BFull:
        isa = {isa, "_Zba_Zbb_Zbc_Zbs_XZbe_XZbf_XZbp_XZbr_XZbt"};
    endcase

    return isa;
  endfunction

  virtual function void build_phase(uvm_phase phase);
    string cosim_log_file;
    bit [31:0] pmp_num_regions;
    bit [31:0] pmp_granularity;
    bit [31:0] mhpm_counter_num;
    bit        secure_ibex;
    bit        icache;

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

    cosim_cfg = core_ibex_cosim_cfg::type_id::create("cosim_cfg", this);

    cosim_cfg.isa_string = get_isa_string();
    cosim_cfg.start_pc =    ((32'h`BOOT_ADDR & ~(32'h0000_00FF)) | 8'h80);
    cosim_cfg.start_mtvec = ((32'h`BOOT_ADDR & ~(32'h0000_00FF)) | 8'h01);
    // TODO: Turn on when not using icache
    cosim_cfg.probe_imem_for_errs = 1'b0;
    void'($value$plusargs("cosim_log_file=%0s", cosim_log_file));
    cosim_cfg.log_file = cosim_log_file;

    if (!uvm_config_db#(bit [31:0])::get(null, "", "PMPNumRegions", pmp_num_regions)) begin
      pmp_num_regions = '0;
    end

    if (!uvm_config_db#(bit [31:0])::get(null, "", "PMPGranularity", pmp_granularity)) begin
      pmp_granularity = '0;
    end

    if (!uvm_config_db#(bit [31:0])::get(null, "", "MHPMCounterNum", mhpm_counter_num)) begin
      mhpm_counter_num = '0;
    end

    if (!uvm_config_db#(bit)::get(null, "", "SecureIbex", secure_ibex)) begin
      secure_ibex = '0;
    end

    if (!uvm_config_db#(bit)::get(null, "", "ICache", icache)) begin
      icache = '0;
    end

    cosim_cfg.pmp_num_regions = pmp_num_regions;
    cosim_cfg.pmp_granularity = pmp_granularity;
    cosim_cfg.mhpm_counter_num = mhpm_counter_num;
    cosim_cfg.relax_cosim_check = cfg.disable_cosim;
    cosim_cfg.secure_ibex = secure_ibex;
    cosim_cfg.icache = icache;

    uvm_config_db#(core_ibex_cosim_cfg)::set(null, "*cosim_agent*", "cosim_cfg", cosim_cfg);

    imem_cfg = ibex_mem_intf_response_agent_cfg::type_id::create("imem_cfg", this);
    dmem_cfg = ibex_mem_intf_response_agent_cfg::type_id::create("dmem_cfg", this);
    // Never create bad integrity bits in response to accessing uninit memory
    // on the Iside, as the Ibex can fetch speculatively.
    imem_cfg.enable_bad_intg_on_uninit_access = 0;
    // By default, enable bad_intg on the Dside (read plusarg to overwrite this behaviour)
    dmem_cfg.enable_bad_intg_on_uninit_access = 1;
    void'($value$plusargs("enable_bad_intg_on_uninit_access=%0d",
                          dmem_cfg.enable_bad_intg_on_uninit_access));
    uvm_config_db#(ibex_mem_intf_response_agent_cfg)::
      set(this, "*instr_if_response_agent*", "cfg", imem_cfg);
    uvm_config_db#(ibex_mem_intf_response_agent_cfg)::
      set(this, "*data_if_response_agent*", "cfg", dmem_cfg);

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
    env.data_if_response_agent.monitor.item_collected_port.connect(
      this.test_done_port.analysis_export);
    env.irq_agent.monitor.irq_port.connect(this.irq_collected_port.analysis_export);
    // Connect the data memory seq to the cosim agent
    // This allows the cosim memory to be updated to match when we generate random data in
    // response to a read from uninit memory.
    vseq.data_intf_seq.cosim_agent = env.cosim_agent;
  endfunction

  virtual task run_phase(uvm_phase phase);
    enable_irq_seq = cfg.enable_irq_single_seq || cfg.enable_irq_multiple_seq;
    phase.raise_objection(this);
    cur_run_phase = phase;
    dut_vif.dut_cb.fetch_enable <= ibex_pkg::IbexMuBiOff;
    clk_vif.wait_clks(100);

    void'($value$plusargs("bin=%0s", binary));
    if (binary == "")
      `uvm_fatal(get_full_name(), "Please specify test binary by +bin=binary_name")
    load_binary_to_mems();
    `uvm_info(get_full_name(), $sformatf("Running test binary : %0s", binary), UVM_LOW)

    dut_vif.dut_cb.fetch_enable <= ibex_pkg::IbexMuBiOn;
    fork
      send_stimulus();
      handle_reset();
    join_none
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

  // Backdoor-load the test binary file into the memory models of both the DUT and the cosimulated ISS
  function void load_binary_to_mems();
    bit [31:0]  addr = 32'h`BOOT_ADDR;
    load_binary_to_dut_mem(addr, binary);             // Populate RTL memory model
    env.cosim_agent.load_binary_to_mem(addr, binary); // Populate ISS memory model
  endfunction

  // Backdoor-load the test binary file into the DUT memory model
  function void load_binary_to_dut_mem(bit[31:0] base_addr, string bin);
     bit [7:0]  r8;
     bit [31:0] addr = base_addr;
     int        bin_fd;
    bin_fd = $fopen(bin,"rb");
    if (!bin_fd)
      `uvm_fatal(get_full_name(), $sformatf("Cannot open file %0s", bin))
    while ($fread(r8, bin_fd)) begin
      `uvm_info(`gfn, $sformatf("Init mem [0x%h] = 0x%0h", addr, r8), UVM_FULL)
      mem.write(addr, r8);
      addr++;
    end
  endfunction

  // Monitor the reset line, and sequence the resetting of the testbench environment
  virtual task handle_reset();
    forever begin
      @(posedge dut_vif.reset);
      `uvm_info(`gfn, "Reset now active", UVM_LOW)
      // Tear-down testbench components
      // Flush FIFOs
      item_collected_port.flush();
      irq_collected_port.flush();

      @(negedge dut_vif.reset);
      `uvm_info(`gfn, "Reset now inactive", UVM_LOW)
      // Build-up testbench components

      // Cosim must be re-initialized before loading the memory
      env.reset();
      load_binary_to_mems(); // Backdoor-load, 0-time
    end
  endtask : handle_reset

  // Watch for all of the different critera for test pass/failure here
  virtual task wait_for_test_done();
    longint timeout_timestamp, ts;
    bit result;

    fork
      // - Use a RISCV_DV handshake signature to end the test.
      // This process uses a different signature address (cfg.signature_addr - 0x4)
      // Make use of the 'test_done_port' which subscribes to all memory interface items.
      // We can then watch for the correct message in isolation.
      begin
        wait_for_mem_txn((cfg.signature_addr - 4'h4), TEST_RESULT, test_done_port);
        result = signature_data_q.pop_front();
        if (result == TEST_PASS) begin
          `uvm_info(`gfn, "Test done due to RISCV-DV handshake (payload=TEST_PASS)", UVM_LOW)
        end else if (result == TEST_FAIL) begin
          `uvm_fatal(`gfn, "Test failed due to RISCV-DV handshake (payload=TEST_FAIL)")
        end else begin
          `uvm_fatal(`gfn, "Incorrectly formed handshake received at test-control address.")
        end
      end
      // - End the test if we see too many of the following...
      //   - double_faults
      begin
        if (cfg.enable_double_fault_detector) begin
          env.scoreboard.dfd_wait_for_pass_events();
          if (cfg.is_double_fault_detected_fatal) begin
            `uvm_fatal(`gfn, "Fatal threshold for double_fault detector reached.")
          end
          // If we get here, join this fork to end the test gracefully.
          `uvm_info(`gfn, "Test done due to double_fault detector.", UVM_LOW)
        end else begin
          wait (test_done == 1'b1);
        end
      end
      // - End the test by timeout if it doesn't terminate within a reasonable time.
      begin
        clk_vif.wait_clks(timeout_in_cycles);
        `uvm_fatal(`gfn, "TEST TIMEOUT!!")
      end
      // - End the test gracefully by wall-clock timeout (gather coverage etc.)
      //   The plusarg 'test_timeout_s' can be used to set this value.
      begin
        void'($value$plusargs("test_timeout_s=%0d", timeout_seconds));
        `uvm_info(`gfn,
                  $sformatf("Test wall-clock timeout is set to : %0ds", timeout_seconds),
                  UVM_LOW)
        timeout_timestamp = get_unix_timestamp() + timeout_seconds;
        forever begin
          // Check the wall-clock every 1000us of simulation time.
          #1000us;
          ts = get_unix_timestamp();
          if (ts >= timeout_timestamp) break;
        end

        if (cfg.is_timeout_s_fatal) begin
          `uvm_fatal(`gfn,
                     $sformatf("Test failed due to wall-clock timeout. [%0ds]", timeout_seconds))
        end else begin
          `uvm_info(`gfn,
                     $sformatf("Test done due to wall-clock timeout. [%0ds]", timeout_seconds),
                     UVM_LOW)
        end
      end
      begin
        wait_for_custom_test_done();
      end
    join_any

    test_done = 1'b1;
    vseq.stop();
    check_perf_stats();
    // De-assert fetch enable to finish the test
    clk_vif.wait_clks(10);
    dut_vif.dut_cb.fetch_enable <= ibex_pkg::IbexMuBiOff;
    // Wait some time for the remaining instruction to finish
    clk_vif.wait_clks(3000);
  endtask


  virtual task wait_for_mem_txn(
    input bit [ibex_mem_intf_agent_pkg::ADDR_WIDTH-1:0] ref_addr,
    input signature_type_t ref_type,
    input uvm_tlm_analysis_fifo #(ibex_mem_intf_seq_item) txn_port = item_collected_port
    );

    ibex_mem_intf_seq_item mem_txn;
    `uvm_info(`gfn, $sformatf("Awaiting riscv-dv handshake at 0x%0h, Type : %0s",
                              ref_addr, ref_type), UVM_HIGH)
    forever begin
      // The first write to this address is guaranteed to contain the signature type in bits [7:0]
      txn_port.get(mem_txn);
      if (mem_txn.addr       == ref_addr &&
          mem_txn.data[7:0] === ref_type &&
          mem_txn.read_write == WRITE) begin
        `uvm_info(`gfn, $sformatf("riscv-dv handshake received at 0x%0h, Type : %0s",
                                  ref_addr, ref_type), UVM_HIGH)
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
                txn_port.get(mem_txn);
              end while(!(mem_txn.addr == ref_addr && mem_txn.read_write == WRITE));
              signature_data_q.push_back(mem_txn.data);
            end
          end
          // The next write to this address is guaranteed to be the data held in the CSR
          WRITE_CSR: begin
            signature_data_q.push_back(signature_data >> 8);
            do begin
              txn_port.get(mem_txn);
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
    fork begin : isolation_fork
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
    end join
    cur_run_phase.drop_objection(this);
  endtask

  // Waits for a write to the address of the specified CSR and retrieves the csr data
  virtual task wait_for_csr_write(csr_num_e csr, int timeout = 9999999);
    bit [11:0] csr_addr;
    cur_run_phase.raise_objection(this);
    fork begin : isolation_fork
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
    end join
    cur_run_phase.drop_objection(this);
  endtask

  // Waits until the next time the given core_status is written to the signature address
  virtual task wait_for_core_status(core_status_t core_status);
    do begin
      wait_for_mem_txn(cfg.signature_addr, CORE_STATUS);
      signature_data = signature_data_q.pop_front();
    end while (signature_data != core_status);
  endtask

  virtual task wait_for_core_exception(ibex_pkg::exc_cause_t exc_cause);
    wait(dut_vif.ctrl_fsm_cs == ibex_pkg::FLUSH && dut_vif.exc_cause == exc_cause &&
      dut_vif.csr_save_cause);
    wait(dut_vif.ctrl_fsm_cs != ibex_pkg::FLUSH);
  endtask

  virtual task wait_for_custom_test_done();
    wait (test_done == 1'b1);
  endtask

endclass
