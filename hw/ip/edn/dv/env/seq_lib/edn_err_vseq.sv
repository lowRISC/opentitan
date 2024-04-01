// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test ERR_CODE fields asserted as expected, as well as the ERR_CODE_TEST register

class edn_err_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_err_vseq)

  `uvm_object_new

  push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)   m_endpoint_pull_seq;

  bit [csrng_pkg::GENBITS_BUS_WIDTH - 1:0]      genbits;
  bit [entropy_src_pkg::FIPS_BUS_WIDTH - 1:0]   fips;
  bit [edn_pkg::ENDPOINT_BUS_WIDTH - 1:0]       edn_bus[MAX_NUM_ENDPOINTS];
  uint                                          endpoint_port;

  // Await a randomly selected state of the edn_ack_sm at index `idx`.  If the state is not reached
  // within `timeout_clks` clock cycles, the task also returns.  This task returns immediately with
  // a chance of 100 - `await_pct` percent.
  task await_random_ack_sm_state(int timeout_clks = 1_000, int await_pct = 90,
                                 hw_req_mode_e mode);
    string state_path;
    state_ack_e exp_state;
    state_path = cfg.edn_vif.sm_err_path("edn_ack_sm", endpoint_port);

    if ($urandom_range(100, 1) > await_pct) begin
      // Don't wait if number randomly sampled between 1 and 100 exceeds the await percentage.
      return;
    end

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(exp_state, exp_state inside {EndPointClear,
                                                                    DataWait,
                                                                    AckPls};)

    `uvm_info(`gfn, $sformatf("Waiting for ack_sm[%0d] to reach state %09b",
                              endpoint_port, exp_state), UVM_HIGH)
    start_transition_to_ack_state(exp_state, mode);
    `DV_SPINWAIT_EXIT(
      forever begin
        uvm_hdl_data_t val;
        state_ack_e act_state;
        cfg.clk_rst_vif.wait_n_clks(1);
        `DV_CHECK(uvm_hdl_read(state_path, val))
        act_state = state_ack_e'(val);
        if (act_state == exp_state) break;
      end
      `uvm_info(`gfn, $sformatf("State reached"), UVM_HIGH),
      // Or exit when the timeout (in clock cycles) has been reached.
      cfg.clk_rst_vif.wait_n_clks(timeout_clks);
      `uvm_info(`gfn, $sformatf("Timed out waiting for ack_sm state %09b", exp_state), UVM_HIGH)
    )
  endtask

  // Await a randomly selected state of edn_main_sm that should be reachable in EDN's current mode.
  // If the state is not reached within `timeout_clks` clock cycles, the task also returns.  This
  // task returns immediately with a chance of 100 - `await_pct` percent.
  task await_random_main_sm_state(int timeout_clks = 1_000, int await_pct = 90,
                                  hw_req_mode_e mode);
    string state_path;
    state_e exp_state;
    state_path = cfg.edn_vif.sm_err_path("edn_main_sm");

    if ($urandom_range(100, 1) > await_pct) begin
      // Don't wait if number randomly sampled between 1 and 100 exceeds the await percentage.
      return;
    end

    if (cfg.boot_req_mode == MuBi4True) begin
      // If EDN is configured in Boot mode, randomly select one of the Boot states.
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(exp_state,
                                         exp_state inside {BootLoadIns, BootInsAckWait, BootLoadGen,
                                                           BootGenAckWait, BootPulse, BootDone};)
    end else if (cfg.auto_req_mode == MuBi4True) begin
      // If instead EDN is configured in Auto mode, randomly select one of the Auto states.
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(exp_state,
                                         exp_state inside {AutoLoadIns, AutoFirstAckWait,
                                                           AutoAckWait, AutoDispatch,
                                                           AutoCaptGenCnt, AutoSendGenCmd,
                                                           AutoCaptReseedCnt, AutoSendReseedCmd};)
    end else begin
      // If EDN is configured neither in Boot nor in Auto mode, select the SW state.
      exp_state = SWPortMode;
    end

    `uvm_info(`gfn, $sformatf("Waiting for main_sm to reach state %s", exp_state.name()), UVM_HIGH)
    start_transition_to_main_sm_state(exp_state, mode);
    `DV_SPINWAIT_EXIT(
      forever begin
        uvm_hdl_data_t val;
        state_e act_state;
        cfg.clk_rst_vif.wait_n_clks(1);
        `DV_CHECK(uvm_hdl_read(state_path, val))
        act_state = state_e'(val);
        if (act_state == exp_state) break;
      end
      `uvm_info(`gfn, $sformatf("State reached"), UVM_HIGH),
      // Or exit when the timeout (in clock cycles) has been reached.
      cfg.clk_rst_vif.wait_n_clks(timeout_clks);
      `uvm_info(`gfn, $sformatf("Timed out waiting for main_sm state %s", exp_state.name()),
                UVM_HIGH)
    )
  endtask

  task start_transition_to_ack_state(state_ack_e exp_state, hw_req_mode_e mode);
    // Create background thread that transitions the ack sm to the expected state.
    // INS and GEN commands are only needed if we are not waiting for EndPointClear or DataWait.
    if (!exp_state inside {EndPointClear, DataWait}) begin
      fork
        begin
          if (cfg.boot_req_mode != MuBi4True) begin
            // Send INS cmd to start the auto/SW mode operation.
            wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(csrng_pkg::INS),
                   .clen(0), .flags(MuBi4False), .glen(0), .mode(mode));
          end
          if (cfg.auto_req_mode != MuBi4True && cfg.boot_req_mode != MuBi4True) begin
            // In SW mode send a GEN command to transition through all possible states.
            // Send GEN cmd with GLEN = 1 (request single genbits).
            wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(csrng_pkg::GEN),
                   .clen(0), .flags(MuBi4False), .glen(1), .mode(mode));
          end
        end
      join_none
    end
  endtask

  task start_transition_to_main_sm_state(state_e exp_state, edn_env_pkg::hw_req_mode_e mode);
    // Create background thread that transitions the main sm to the expected state.
    fork
      begin
        // Send an instantiate command if we are in auto mode and the expected state
        // is not AutoLoadIns. All the other state transitions happen automatically.
        if (cfg.boot_req_mode != MuBi4True && cfg.auto_req_mode == MuBi4True
            && exp_state != AutoLoadIns) begin
          // Send INS cmd to start the auto/SW mode operation.
          // Set wait_cmd_req_done to 0 since we don't want to wait for the ack.
          wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(csrng_pkg::INS), .clen(0),
                 .flags(MuBi4False), .glen(0), .mode(mode), .wait_for_ack(0));
        end
      end
    join_none
  endtask

  task body();
    hw_req_mode_e              mode;
    bit [5:0]                  err_code_test_bit;
    string                     path, path1, path2;
    bit                        value1, value2;
    string                     fifo_name;
    int                        first_index, last_index;
    string                     fifo_base_path;
    string                     path_exts [4] = {"push", "full", "pop", "not_empty"};
    string                     fifo_forced_paths [4];
    bit                        fifo_forced_values [4] = {1'b1, 1'b1, 1'b1, 1'b0};
    string                     fifo_err_path [2][string];
    bit                        fifo_err_value [2][string];
    string                     path_key;
    string                     reg_name, fld_name;
    uvm_reg                    csr;
    uvm_reg_field              fld;
    bit [31:0]                 backdoor_err_code_val;

    fifo_err_path[0] = '{"write": "push", "read": "pop", "state": "full"};
    fifo_err_path[1] = '{"write": "full", "read": "not_empty", "state": "not_empty"};
    fifo_err_value[0] = '{"write": 1'b1, "read": 1'b1, "state": 1'b1};
    fifo_err_value[1] = '{"write": 1'b1, "read": 1'b0, "state": 1'b0};

    // Turn off fatal alert check
    expect_fatal_alerts = 1'b1;

    // Turn off assertions
    $assertoff(0, "tb.dut.u_edn_core.u_prim_fifo_sync_rescmd.DataKnown_A");
    $assertoff(0, "tb.dut.u_edn_core.u_prim_fifo_sync_gencmd.DataKnown_A");
    cfg.edn_assert_vif.assert_off();

    reg_name = "err_code";
    csr = ral.get_reg_by_name(reg_name);
    fld_name = cfg.which_err_code.name();

    first_index = find_index("_", fld_name, "first");
    last_index = find_index("_", fld_name, "last");

    // Determine the operational mode.
    if (cfg.boot_req_mode == MuBi4True) begin
      mode = edn_env_pkg::BootReqMode;
    end else if (cfg.auto_req_mode == MuBi4True) begin
      mode = edn_env_pkg::AutoReqMode;
    end else begin // SW mode
      mode = edn_env_pkg::SwMode;
    end

    // Disable the EDN.
    wait_no_outstanding_access();
    // CSRNG requests will drop if disablement is sent.
    // The corresponding assertions can be disabled shortly since CSRNG must be disabled
    // any time the EDN is disabled according to specification.
    // https://opentitan.org/book/hw/ip/edn/doc/programmers_guide.html
    $assertoff(0, "tb.csrng_if.cmd_push_if.H_DataStableWhenValidAndNotReady_A");
    $assertoff(0, "tb.csrng_if.cmd_push_if.ValidHighUntilReady_A");
    ral.ctrl.edn_enable.set(prim_mubi_pkg::MuBi4False);
    csr_update(.csr(ral.ctrl));
    // Notify the driver that the EDN was disabled.
    cfg.edn_vif.drive_edn_disable(1);
    // In Auto mode, minimize number of requests between reseeds and set the reseed command.
    if (mode == edn_env_pkg::AutoReqMode) begin
      csr_wr(.ptr(ral.max_num_reqs_between_reseeds), .value(1));
      wr_cmd(.cmd_type(edn_env_pkg::AutoRes), .acmd(csrng_pkg::RES), .clen(0),
             .flags(MuBi4False), .mode(mode));
    end
    // Write auto mode commands to the FIFOs that minimize the time it takes to reach the desired state.
    wr_cmd(.cmd_type(edn_env_pkg::AutoRes), .acmd(csrng_pkg::RES), .clen(0), .flags(MuBi4False),
            .glen(1), .mode(mode));
    wr_cmd(.cmd_type(edn_env_pkg::AutoGen), .acmd(csrng_pkg::GEN), .clen(0), .flags(MuBi4False),
            .glen(1), .mode(mode));
    // Enable the EDN.
    ral.ctrl.edn_enable.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.ctrl));
    // Notify the driver that the EDN was enabled.
    cfg.edn_vif.drive_edn_disable(0);
    // Reenable assertions since the EDN is now enabled again.
    $asserton(0, "tb.csrng_if.cmd_push_if.H_DataStableWhenValidAndNotReady_A");
    $asserton(0, "tb.csrng_if.cmd_push_if.ValidHighUntilReady_A");

    // Load genbits data
    m_endpoint_pull_seq = push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)::type_id::
        create("m_endpoint_pull_seq");
    `DV_CHECK_STD_RANDOMIZE_FATAL(fips)
    `DV_CHECK_STD_RANDOMIZE_FATAL(genbits)
    cfg.m_csrng_agent_cfg.m_genbits_push_agent_cfg.add_h_user_data({fips, genbits});

    // Create background thread that does endpoint requests.
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(endpoint_port,
                                       endpoint_port inside { [0:cfg.num_endpoints - 1] };)
    fork
      m_endpoint_pull_seq.start(p_sequencer.endpoint_sequencer_h[endpoint_port]);
    join_none
    // main_sm is more complex, so the random selection is biased towards it.
    if ((cfg.which_err_code == edn_ack_sm_err) || ($urandom_range(10, 1) < 8)) begin
      // Errors in ack_sm can be used to trigger transitions to the Error state in main_sm.
      await_random_main_sm_state(.mode(mode));
    end else begin
      // Errors in main_sm can be used to trigger transitions to the Error state in ack_sm.
      await_random_ack_sm_state(.mode(mode));
    end

    // Insert the selected error.
    `uvm_info(`gfn, $sformatf("which_err_code = %s", cfg.which_err_code.name()), UVM_HIGH)
    // CSRNG requests can drop if the SM reaches an error state.
    // The corresponding assertions can be disabled shortly since CSRNG must be disabled
    // any time the EDN is disabled according to specification.
    // https://opentitan.org/book/hw/ip/edn/doc/programmers_guide.html
    $assertoff(0, "tb.csrng_if.cmd_push_if.H_DataStableWhenValidAndNotReady_A");
    $assertoff(0, "tb.csrng_if.cmd_push_if.ValidHighUntilReady_A");
    case (cfg.which_err_code) inside
      sfifo_rescmd_err, sfifo_gencmd_err, sfifo_output_err: begin
        fld = csr.get_field_by_name(fld_name);
        fifo_base_path = fld_name.substr(0, last_index-1);

        foreach (path_exts[i]) begin
          fifo_forced_paths[i] = cfg.edn_vif.fifo_err_path(fifo_base_path, path_exts[i]);
        end
        force_all_fifo_errs(fifo_forced_paths, fifo_forced_values, path_exts, fld,
                            1'b1, cfg.which_fifo_err);
        if (cfg.en_cov) begin
          csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
          cov_vif.cg_error_sample(.err_code(backdoor_err_code_val));
        end
      end
      edn_ack_sm_err, edn_main_sm_err: begin
        fld = csr.get_field_by_name(fld_name);
        path = cfg.edn_vif.sm_err_path(fld_name.substr(0, last_index-1));
        force_path_err(path, 6'b0, fld, 1'b1);
        if (cfg.en_cov) begin
          csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
          cov_vif.cg_error_sample(.err_code(backdoor_err_code_val));
        end
      end
      edn_cntr_err: begin
        fld = csr.get_field_by_name(fld_name);
        path = cfg.edn_vif.cntr_err_path();
        force_path_err(path, 6'b000001, fld, 1'b1);
        // Verify EDN.MAIN_SM.CTR.LOCAL_ESC
        csr_rd_check(.ptr(ral.err_code.edn_cntr_err), .compare_value(1'b1));
        if (cfg.en_cov) begin
          csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
          cov_vif.cg_error_sample(.err_code(backdoor_err_code_val));
        end
      end
      fifo_write_err, fifo_read_err, fifo_state_err: begin
        fld = csr.get_field_by_name(fld_name);
        fifo_name = cfg.which_fifo.name();
        path_key = fld_name.substr(first_index+1, last_index-1);

        path1 = cfg.edn_vif.fifo_err_path(fifo_name, fifo_err_path[0][path_key]);
        path2 = cfg.edn_vif.fifo_err_path(fifo_name, fifo_err_path[1][path_key]);
        value1 = fifo_err_value[0][path_key];
        value2 = fifo_err_value[1][path_key];
        force_fifo_err(path1, path2, value1, value2, fld, 1'b1);
        if (cfg.en_cov) begin
          csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
          cov_vif.cg_error_sample(.err_code(backdoor_err_code_val));
        end
      end
      sfifo_rescmd_err_test, sfifo_gencmd_err_test, sfifo_output_err_test, edn_ack_sm_err_test,
      edn_main_sm_err_test, edn_cntr_err_test, fifo_write_err_test, fifo_read_err_test,
      fifo_state_err_test: begin
        fld = csr.get_field_by_name(fld_name.substr(0, last_index-1));
        err_code_test_bit = fld.get_lsb_pos();
        csr_wr(.ptr(ral.err_code_test.err_code_test), .value(err_code_test_bit));
        cfg.clk_rst_vif.wait_clks(50);
        csr_rd_check(.ptr(fld), .compare_value(1'b1));
        if (cfg.which_err_code == edn_cntr_err_test) begin
          // Verify EDN.MAIN_SM.CTR.LOCAL_ESC
          csr_rd_check(.ptr(ral.err_code.edn_main_sm_err), .compare_value(1'b1));
          if (cfg.en_cov) begin
            csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
            cov_vif.cg_error_sample(.err_code(backdoor_err_code_val));
          end
          // Clear interrupt_enable
          csr_wr(.ptr(ral.intr_enable), .value(32'd0));
          ral.ctrl.edn_enable.set(prim_mubi_pkg::MuBi4False);
          ral.ctrl.cmd_fifo_rst.set(prim_mubi_pkg::MuBi4True);
          csr_update(.csr(ral.ctrl));
          // Expect/Clear interrupt bit
          check_interrupts(.interrupts((1 << FifoErr)), .check_set(1'b1));
        end
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid case! (bug in environment)")
      end
    endcase // case (cfg.which_err_code)

    // Turn assertions back on
    $asserton(0, "tb.csrng_if.cmd_push_if.H_DataStableWhenValidAndNotReady_A");
    $asserton(0, "tb.csrng_if.cmd_push_if.ValidHighUntilReady_A");
    cfg.edn_assert_vif.assert_on();
  endtask

endclass : edn_err_vseq
