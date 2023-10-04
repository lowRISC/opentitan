// Copyright lowRISC contributors.
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
  uint                                                    endpoint_port;

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
    exp_recov_alert_sts[ral.recov_alert_sts.edn_bus_cmp_alert.get_lsb_pos()] = 1;
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
    fld = csr.get_field_by_name({fld_name.substr(first_index+1, fld_name.len()-1), "_field_alert"});

    exp_recov_alert_sts = 32'b0;
    exp_recov_alert_sts[fld.get_lsb_pos()] = 1;
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(exp_recov_alert_sts));
    if (cfg.en_cov) begin
      cov_vif.cg_alert_sample(.recov_alert_sts(exp_recov_alert_sts));
    end

    // Write valid values
    ral.ctrl.edn_enable.set(prim_mubi_pkg::MuBi4True);
    ral.ctrl.boot_req_mode.set(prim_mubi_pkg::MuBi4False);
    ral.ctrl.auto_req_mode.set(prim_mubi_pkg::MuBi4False);
    ral.ctrl.cmd_fifo_rst.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.ctrl));

    // Clear recov_alert_sts register
    csr_wr(.ptr(ral.recov_alert_sts), .value(32'b0));

    // Check recov_alert_sts register
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
