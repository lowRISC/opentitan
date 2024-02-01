// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test recoverable alerts with invalid mubi data type inputs and edn_bus_cmp_alert
class edn_alert_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_alert_vseq)

  `uvm_object_new

  push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)   m_endpoint_pull_seq;
  bit [csrng_pkg::GENBITS_BUS_WIDTH - 1:0]                genbits;
  bit [entropy_src_pkg::FIPS_BUS_WIDTH - 1:0]             fips;
  bit [31:0]                                              exp_recov_alert_sts;
  bit [31:0]                                              value;
  uint                                                    endpoint_port;


  task start_transition_to_main_sm_state(state_e exp_state);
    // Create background thread that transitions the main sm to the expected state.
    fork
      begin
        // Send an instantiate command if we are in auto mode.
        if (cfg.boot_req_mode != MuBi4True && cfg.auto_req_mode == MuBi4True) begin
          // Send INS cmd to start the auto/SW mode operation.
          wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(csrng_pkg::INS), .clen(0),
                 .flags(MuBi4False), .glen(0), .mode(edn_env_pkg::AutoReqMode), .wait_for_ack(1));
        end
      end
    join_none
  endtask

  task test_edn_cs_sts_alert();
    string state_path;
    string genbits_valid_path;
    state_e exp_state;
    bit [31:0] exp_hw_cmd_sts;
    bit send_generate;
    state_path = cfg.edn_vif.sm_err_path("edn_main_sm");
    genbits_valid_path = cfg.edn_vif.genbits_valid_path();
    // Re-randomize config without invalid mubi values and without clearing the FIFOs.
    cfg.use_invalid_mubi  = 0;
    cfg.cmd_fifo_rst_pct  = 0;
    `DV_CHECK_RANDOMIZE_FATAL(cfg)

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(endpoint_port,
                                       endpoint_port inside { [0:cfg.num_endpoints - 1] };)

    m_endpoint_pull_seq = push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)::type_id::
        create("m_endpoint_pull_seq");

    if (cfg.boot_req_mode == MuBi4True) begin
      // If EDN is configured in Boot mode, randomly select one of the Boot states.
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(exp_state,
                                         exp_state inside {BootLoadIns, BootInsAckWait,
                                                           BootLoadGen, BootGenAckWait,
                                                           BootPulse, BootDone,
                                                           BootLoadUni};)
      // Set the boot generate command to request the minimal amount of entropy.
      wr_cmd(.cmd_type(edn_env_pkg::BootGen), .acmd(csrng_pkg::GEN), .clen(0), .flags(MuBi4False),
             .glen(1), .mode(edn_env_pkg::BootReqMode));
    end else if (cfg.auto_req_mode == MuBi4True) begin
      // If instead EDN is configured in auto mode, randomly select one of the auto mode states.
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(exp_state,
                                         exp_state inside {AutoAckWait, AutoDispatch,
                                                           AutoCaptGenCnt, AutoSendGenCmd,
                                                           AutoCaptReseedCnt, AutoSendReseedCmd};)
      // In auto mode, minimize number of requests between reseeds and set the reseed command.
      csr_wr(.ptr(ral.max_num_reqs_between_reseeds), .value(1));
      wr_cmd(.cmd_type(edn_env_pkg::AutoRes), .acmd(csrng_pkg::RES), .clen(0),
             .flags(MuBi4False), .mode(edn_env_pkg::AutoReqMode));
      wr_cmd(.cmd_type(edn_env_pkg::AutoGen), .acmd(csrng_pkg::GEN), .clen(0), .flags(MuBi4False),
             .glen(1), .mode(edn_env_pkg::AutoReqMode));
    end

    // Wait for the EDN main SM to enter the desired state and apply the rsp_sts_err setting to
    // make the next CSRNG acknowledgement return an error.
    fork
      `DV_SPINWAIT(
        `uvm_info(`gfn, $sformatf("Waiting for main_sm to reach state %s",
                                  exp_state.name()), UVM_HIGH)
        forever begin
          uvm_hdl_data_t val;
          state_e act_state;
          cfg.clk_rst_vif.wait_n_clks(1);
          `DV_CHECK(uvm_hdl_read(state_path, val))
          act_state = state_e'(val);
          if (act_state == exp_state) break;
        end
        `uvm_info(`gfn, $sformatf("State reached"), UVM_HIGH)
        // The next acknowledgement should return an error status.
        cfg.m_csrng_agent_cfg.rsp_sts_err = 1;
      )
    join_none

    // Set the EDN ctrl values.
    ral.ctrl.edn_enable.set(cfg.enable);
    ral.ctrl.boot_req_mode.set(cfg.boot_req_mode);
    ral.ctrl.auto_req_mode.set(cfg.auto_req_mode);
    ral.ctrl.cmd_fifo_rst.set(cfg.cmd_fifo_rst);
    csr_update(.csr(ral.ctrl));
    // Read the hw_cmd_sts for coverage.
    csr_rd(.ptr(ral.hw_cmd_sts), .value(value));
    // If coverage is enabled, record the values of the hw_cmd_sts register.
    if (cfg.en_cov) begin
      cov_vif.cg_edn_hw_cmd_sts_sample(.boot_mode(value[hw_cmd_boot_mode]),
                                       .auto_mode(value[hw_cmd_auto_mode]),
                                       .cmd_sts(value[hw_cmd_sts]),
                                       .cmd_ack(value[hw_cmd_ack]),
                                       .acmd(csrng_pkg::acmd_e'(value[hw_cmd_type+:4])));
    end
    // Issue the commands that are needed to get to exp_state in a fork.
    start_transition_to_main_sm_state(exp_state);
    send_generate = (exp_state inside {BootLoadGen, BootGenAckWait, BootPulse, BootDone,
                                       BootLoadUni, AutoCaptReseedCnt, AutoSendReseedCmd});

    // Load constant genbits data to complete the generate request if needed.
    if (send_generate) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(fips)
      `DV_CHECK_STD_RANDOMIZE_FATAL(genbits)
      cfg.m_csrng_agent_cfg.m_genbits_push_agent_cfg.add_h_user_data({fips, genbits});
    end
    // Disable the boot mode to trigger the uninstaniate command if needed.
    if (exp_state inside {BootLoadGen, BootGenAckWait, BootPulse, BootDone, BootLoadUni}) begin
      ral.ctrl.boot_req_mode.set(MuBi4False);
      csr_update(.csr(ral.ctrl));
    end

    // Wait for the CSRNG error status response to propagate through the EDN
    // to the hw_cmd_sts register.
    csr_spinwait(.ptr(ral.hw_cmd_sts.cmd_sts), .exp_data(1'b1), .backdoor(1'b1));
    cfg.clk_rst_vif.wait_clks(10);
    // Expect the csrng_ack_err bit to be set in the recov_alert_sts register.
    exp_recov_alert_sts = 32'b0;
    exp_recov_alert_sts[csrng_ack_err] = 1;
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(exp_recov_alert_sts));
    // Check hw_cmd_sts in scoreboard.
    exp_hw_cmd_sts[hw_cmd_boot_mode] = (cfg.boot_req_mode == MuBi4True) ? 1'b1 : 1'b0;
    exp_hw_cmd_sts[hw_cmd_auto_mode] = (cfg.auto_req_mode == MuBi4True) ? 1'b1 : 1'b0;
    exp_hw_cmd_sts[hw_cmd_sts] = 1'b1;
    exp_hw_cmd_sts[hw_cmd_ack] = 1'b1;
    exp_hw_cmd_sts[hw_cmd_type+:4] =
        (exp_state inside {BootLoadIns, BootInsAckWait}) ? csrng_pkg::INS :
        (exp_state inside {BootPulse, BootDone, BootLoadUni}) ? csrng_pkg::UNI :
        (exp_state inside {AutoCaptReseedCnt, AutoSendReseedCmd}) ? csrng_pkg::RES :
        csrng_pkg::GEN;
    csr_rd_check(.ptr(ral.hw_cmd_sts), .compare_value(exp_hw_cmd_sts));
    // If coverage is enabled, record the values of the hw_cmd_sts register.
    if (cfg.en_cov) begin
      cov_vif.cg_edn_hw_cmd_sts_sample(.boot_mode(exp_hw_cmd_sts[hw_cmd_boot_mode]),
                                       .auto_mode(exp_hw_cmd_sts[hw_cmd_auto_mode]),
                                       .cmd_sts(exp_hw_cmd_sts[hw_cmd_sts]),
                                       .cmd_ack(exp_hw_cmd_sts[hw_cmd_ack]),
                                       .acmd(csrng_pkg::acmd_e'(exp_hw_cmd_sts[hw_cmd_type+:4])));
    end
    csr_rd_check(.ptr(ral.main_sm_state), .compare_value(edn_pkg::RejectCsrngEntropy));
    // See if we can request some data if the generate has been issued.
    if (send_generate) begin
      m_endpoint_pull_seq.num_trans =
          csrng_pkg::GENBITS_BUS_WIDTH/edn_pkg::ENDPOINT_BUS_WIDTH;
      m_endpoint_pull_seq.start(p_sequencer.endpoint_sequencer_h[endpoint_port]);
    end
    // From now on we want the CSRNG status responses to be valid again.
    cfg.m_csrng_agent_cfg.rsp_sts_err = 0;
    // Force the genbits valid signal to high and verify that the EDN does not accept
    // any further genbits.
    `DV_SPINWAIT_EXIT(`DV_CHECK(uvm_hdl_force(cfg.edn_vif.genbits_valid_path(), 1'b1));
                      cfg.clk_rst_vif.wait_clks(100);
                      `DV_CHECK(uvm_hdl_release(cfg.edn_vif.genbits_valid_path()));,
                      wait(cfg.m_csrng_agent_cfg.vif.genbits_push_if.ready);
                      `uvm_fatal(`gfn, $sformatf({"The genbits ready signal should stay low after",
                                                  " receiving an error sts signal from CSRNG."})))
    // Clear the genbits user data to prepare for the next test.
    cfg.m_csrng_agent_cfg.m_genbits_push_agent_cfg.clear_h_user_data();
    // Disable the EDN to prepare for the next test.
    value = {prim_mubi_pkg::MuBi4False,  // edn_enable
             prim_mubi_pkg::MuBi4False,  // boot_req_mode
             prim_mubi_pkg::MuBi4False,  // auto_req_mode
             prim_mubi_pkg::MuBi4False}; // cmd_fifo_rst
    csr_wr(.ptr(ral.ctrl), .value(value));
  endtask // edn_bus_cmp_alert

  task test_edn_bus_cmp_alert();
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(endpoint_port,
                                       endpoint_port inside { [0:cfg.num_endpoints - 1] };)

    m_endpoint_pull_seq = push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)::type_id::
        create("m_endpoint_pull_seq");

    `DV_CHECK_STD_RANDOMIZE_FATAL(fips)
    `DV_CHECK_STD_RANDOMIZE_FATAL(genbits)

    // Load randomly generated but constant fips and genbits data through this test
    // to induce edn bus cmp alert
    cfg.m_csrng_agent_cfg.m_genbits_push_agent_cfg.add_h_user_data({fips, genbits});

    // Send INS cmd
    wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(csrng_pkg::INS), .clen(0), .flags(MuBi4True),
           .glen(0), .mode(edn_env_pkg::AutoReqMode));

    // Send GEN cmd w/ GLEN 1 (request single genbits)
    wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(csrng_pkg::GEN), .clen(0), .flags(MuBi4True),
           .glen(1), .mode(edn_env_pkg::AutoReqMode));
    // Load constant genbits data
    cfg.m_csrng_agent_cfg.m_genbits_push_agent_cfg.add_h_user_data({fips, genbits});
    // Request data
    m_endpoint_pull_seq.start(p_sequencer.endpoint_sequencer_h[endpoint_port]);

    // Load constant genbits data
    cfg.m_csrng_agent_cfg.m_genbits_push_agent_cfg.add_h_user_data({fips, genbits});
    // Request data
    m_endpoint_pull_seq.start(p_sequencer.endpoint_sequencer_h[endpoint_port]);

    // Load constant genbits data
    cfg.m_csrng_agent_cfg.m_genbits_push_agent_cfg.add_h_user_data({fips, genbits});
    // Request data
    m_endpoint_pull_seq.start(p_sequencer.endpoint_sequencer_h[endpoint_port]);

    // Load constant genbits data
    cfg.m_csrng_agent_cfg.m_genbits_push_agent_cfg.add_h_user_data({fips, genbits});
    // Request data
    m_endpoint_pull_seq.start(p_sequencer.endpoint_sequencer_h[endpoint_port]);

    // Send GEN cmd w/ GLEN 1 (request single genbits)
    wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(csrng_pkg::GEN), .clen(0), .flags(MuBi4True),
           .glen(1), .mode(edn_env_pkg::AutoReqMode));

    // Load constant genbits data
    cfg.m_csrng_agent_cfg.m_genbits_push_agent_cfg.add_h_user_data({fips, genbits});
    // Request data
    m_endpoint_pull_seq.start(p_sequencer.endpoint_sequencer_h[endpoint_port]);

    // Check recov_alert_sts register
    cfg.clk_rst_vif.wait_clks(100);
    exp_recov_alert_sts = 32'b0;
    exp_recov_alert_sts[edn_bus_cmp_alert] = 1;
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(exp_recov_alert_sts));
    if (cfg.en_cov) begin
      cov_vif.cg_alert_sample(.recov_alert_sts(exp_recov_alert_sts));
    end
  endtask // edn_bus_cmp_alert

  task body();
    int           first_index;
    string        reg_name;
    string        fld_name;
    uvm_reg       csr;
    uvm_reg_field fld;

    if (cfg.use_invalid_mubi) begin
      // Turn off DUT assertions so that the corresponding alert can fire
      cfg.edn_assert_vif.assert_off_alert();
    end

    // Depending on the value of cfg.which_invalid_mubi, one of the following ctrl register fields
    // will be set to an invalid MuBI value.
    // Apply the bad settings, and confirm the corresponding alert is fired.
    ral.ctrl.edn_enable.set(cfg.enable);
    ral.ctrl.boot_req_mode.set(cfg.boot_req_mode);
    ral.ctrl.auto_req_mode.set(cfg.auto_req_mode);
    ral.ctrl.cmd_fifo_rst.set(cfg.cmd_fifo_rst);
    csr_update(.csr(ral.ctrl));

    cfg.clk_rst_vif.wait_clks(100);

    // Check the recov_alert_sts register
    reg_name = "recov_alert_sts";
    fld_name = cfg.which_invalid_mubi.name();

    first_index = find_index("_", fld_name, "first");

    csr = ral.get_reg_by_name(reg_name);
    fld = csr.get_field_by_name({fld_name.substr(first_index+1, fld_name.len()-1),
                                 "_field_alert"});

    exp_recov_alert_sts = 32'b0;
    exp_recov_alert_sts[fld.get_lsb_pos()] = 1;
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(exp_recov_alert_sts));
    if (cfg.en_cov) begin
      cov_vif.cg_alert_sample(.recov_alert_sts(exp_recov_alert_sts));
    end

    // CSRNG requests can drop if the EDN is disabled.
    // The corresponding assertions can be disabled shortly since CSRNG must be disabled
    // any time the EDN is disabled according to specification.
    // https://opentitan.org/book/hw/ip/edn/doc/programmers_guide.html
    $assertoff(0, "tb.csrng_if.cmd_push_if.H_DataStableWhenValidAndNotReady_A");
    $assertoff(0, "tb.csrng_if.cmd_push_if.ValidHighUntilReady_A");
    // Set the CTRL register fields back to some valid MuBi4 value.
    value = {prim_mubi_pkg::MuBi4False, // edn_enable
             prim_mubi_pkg::MuBi4False, // boot_req_mode
             prim_mubi_pkg::MuBi4False, // auto_req_mode
             prim_mubi_pkg::MuBi4True}; // cmd_fifo_rst
    csr_wr(.ptr(ral.ctrl), .value(value));
    // Stop clearing the EDN FIFOs.
    csr_wr(.ptr(ral.ctrl.cmd_fifo_rst), .value(prim_mubi_pkg::MuBi4False));
    // Turn the assertions back on.
    $asserton(0, "tb.csrng_if.cmd_push_if.H_DataStableWhenValidAndNotReady_A");
    $asserton(0, "tb.csrng_if.cmd_push_if.ValidHighUntilReady_A");

    // Clear the recov_alert_sts register.
    csr_wr(.ptr(ral.recov_alert_sts), .value(32'b0));
    // Check the recov_alert_sts register.
    cfg.clk_rst_vif.wait_clks(100);
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(0));

    // Start the CSRNG error status response alert test.
    test_edn_cs_sts_alert();

    // Disable the EDN and clear the FIFOs.
    ral.ctrl.edn_enable.set(prim_mubi_pkg::MuBi4False);
    ral.ctrl.boot_req_mode.set(prim_mubi_pkg::MuBi4False);
    ral.ctrl.auto_req_mode.set(prim_mubi_pkg::MuBi4False);
    ral.ctrl.cmd_fifo_rst.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.ctrl));
    csr_wr(.ptr(ral.ctrl.cmd_fifo_rst), .value(prim_mubi_pkg::MuBi4False));
    csr_wr(.ptr(ral.ctrl.edn_enable), .value(prim_mubi_pkg::MuBi4True));

    // Clear the recov_alert_sts register.
    csr_wr(.ptr(ral.recov_alert_sts), .value(32'b0));
    // Check the recov_alert_sts register.
    cfg.clk_rst_vif.wait_clks(100);
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(0));

    // edn_bus_cmp_alert test, verify EDN.CS_RDATA.BUS.CONSISTENCY
    test_edn_bus_cmp_alert();

    cfg.clk_rst_vif.wait_clks(100);

    // Clear the recov_alert_sts register
    csr_wr(.ptr(ral.recov_alert_sts), .value(32'h0));
    // Check the recov_alert_sts register
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(0));

    // Turn assertions back on
    cfg.edn_assert_vif.assert_on_alert();

  endtask

endclass : edn_alert_vseq
