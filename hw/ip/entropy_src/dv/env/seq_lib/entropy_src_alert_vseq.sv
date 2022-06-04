// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test recoverable alerts with invalid mubi data type inputs and
// es_bus_cmp_alert as well as es_main_sm_alert

class entropy_src_alert_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_alert_vseq)

  `uvm_object_new

  push_pull_indefinite_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)        m_rng_push_seq;
  push_pull_indefinite_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH) m_csrng_pull_seq;

  bit [31:0] exp_recov_alert_sts;

  task test_es_thresh_cfg_alert();
    bit [15:0] alert_thresh;
    bit [15:0] alert_thresh_inv;
    // First turn off module_enable to write registers
    csr_wr(.ptr(ral.module_enable), .value(prim_mubi_pkg::MuBi4False));

    `DV_CHECK_STD_RANDOMIZE_FATAL(alert_thresh)
    ral.alert_threshold.alert_threshold.set(alert_thresh);
    ral.alert_threshold.alert_threshold_inv.set(alert_thresh);
    csr_update(.csr(ral.alert_threshold));
    // Check recov_alert_sts register
    exp_recov_alert_sts = 32'b0;
    exp_recov_alert_sts[ral.recov_alert_sts.es_thresh_cfg_alert.get_lsb_pos()] = 1;
    csr_rd_check(.ptr(ral.recov_alert_sts.es_thresh_cfg_alert), .compare_value(1'b1));

    // Write back correct threshold
    alert_thresh_inv = ~alert_thresh;
    ral.alert_threshold.alert_threshold.set(alert_thresh);
    ral.alert_threshold.alert_threshold_inv.set(alert_thresh_inv);
    csr_update(.csr(ral.alert_threshold));

    // Clear recov_alert_sts register
    csr_wr(.ptr(ral.recov_alert_sts), .value(0));

    // Check recov_alert_sts register
    cfg.clk_rst_vif.wait_clks(100);
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(0));
  endtask // test_es_thresh_cfg_alert

  task test_es_bus_cmp_alert();
    int num_reqs = 60;
    // First turn off module_enable to write registers
    csr_wr(.ptr(ral.module_enable), .value(prim_mubi_pkg::MuBi4False));
    // Set the threshold to make health test not to fail
    ral.repcnt_thresholds.fips_thresh.set(16'hfffe);
    ral.repcnt_thresholds.bypass_thresh.set(16'hfffe);
    csr_update(.csr(ral.repcnt_thresholds));

    // configs
    ral.conf.fips_enable.set(prim_mubi_pkg::MuBi4True);
    ral.conf.entropy_data_reg_enable.set(prim_mubi_pkg::MuBi4True);
    ral.conf.threshold_scope.set(prim_mubi_pkg::MuBi4True);
    ral.conf.rng_bit_enable.set(prim_mubi_pkg::MuBi4False);
    csr_update(.csr(ral.conf));
    ral.fw_ov_control.fw_ov_mode.set(prim_mubi_pkg::MuBi4False);
    csr_update(.csr(ral.fw_ov_control));
    ral.entropy_control.es_route.set(prim_mubi_pkg::MuBi4False);
    ral.entropy_control.es_type.set(prim_mubi_pkg::MuBi4False);
    csr_update(.csr(ral.entropy_control));
    ral.module_enable.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.module_enable));

    // Create and start rng host sequence
    m_rng_push_seq = push_pull_indefinite_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");
    m_rng_push_seq.num_trans = num_reqs *
                               entropy_src_pkg::CSRNG_BUS_WIDTH/entropy_src_pkg::RNG_BUS_WIDTH;
    // Use a randomly generated but fixed rng_val through this test to make the entropy bus
    // value keep stable to induce the es_bus_cmp_alert
    `DV_CHECK_STD_RANDOMIZE_FATAL(rng_val)
    for (int i = 0; i < m_rng_push_seq.num_trans; i++) begin
      cfg.m_rng_agent_cfg.add_h_user_data(rng_val);
    end
    // Create csrng host sequence
    m_csrng_pull_seq = push_pull_indefinite_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)::
         type_id::create("m_csrng_pull_seq");
    m_csrng_pull_seq.num_trans = num_reqs;

    fork
      // Start sequences
      m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
      m_csrng_pull_seq.start(p_sequencer.csrng_sequencer_h);

      begin
        cfg.clk_rst_vif.wait_clks(50000);
        // Check the recov_alert_sts register
        csr_rd_check(.ptr(ral.recov_alert_sts.es_bus_cmp_alert), .compare_value(1'b1));

        cfg.clk_rst_vif.wait_clks(1000);
        // Clear the recov_alert_sts register
        csr_wr(.ptr(ral.recov_alert_sts), .value(32'b0));
        // Check the recov_alert_sts register
        csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(0));

        // Stop the sequences
        `uvm_info(`gfn, "Stopping CSRNG seq", UVM_LOW)
        m_csrng_pull_seq.stop(.hard(1));
        m_csrng_pull_seq.wait_for_sequence_state(UVM_FINISHED);
        `uvm_info(`gfn, "Stopping RNG seq", UVM_LOW)
        m_rng_push_seq.stop(.hard(0));
        m_rng_push_seq.wait_for_sequence_state(UVM_FINISHED);
        `uvm_info(`gfn, "Exiting test body.", UVM_LOW)
      end
    join
  endtask // test_es_bus_cmp_alert

  task test_es_main_sm_alert();
    // First turn off module_enable to write registers
    csr_wr(.ptr(ral.module_enable), .value(prim_mubi_pkg::MuBi4False));
    // Set some thresholds to cause health test to fail
    ral.repcnt_thresholds.fips_thresh.set(16'h0008);
    ral.repcnt_thresholds.bypass_thresh.set(16'h0008);
    csr_update(.csr(ral.repcnt_thresholds));
    // enable
    ral.conf.fips_enable.set(prim_mubi_pkg::MuBi4True);
    ral.conf.entropy_data_reg_enable.set(prim_mubi_pkg::MuBi4True);
    ral.conf.threshold_scope.set(prim_mubi_pkg::MuBi4True);
    ral.conf.rng_bit_enable.set(prim_mubi_pkg::MuBi4False);
    csr_update(.csr(ral.conf));
    ral.fw_ov_control.fw_ov_mode.set(prim_mubi_pkg::MuBi4False);
    csr_update(.csr(ral.fw_ov_control));
    ral.entropy_control.es_route.set(prim_mubi_pkg::MuBi4False);
    csr_update(.csr(ral.entropy_control));
    ral.module_enable.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.module_enable));

    // Create rng host sequence
    m_rng_push_seq = push_pull_indefinite_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");
    m_rng_push_seq.num_trans = 8*entropy_src_pkg::CSRNG_BUS_WIDTH/entropy_src_pkg::RNG_BUS_WIDTH;
    // Use randomly generated but fixed rng_val through this test  to cause the repcnt health
    // test to fail
    `DV_CHECK_STD_RANDOMIZE_FATAL(rng_val)
    for (int i = 0; i < m_rng_push_seq.num_trans; i++) begin
      cfg.m_rng_agent_cfg.add_h_user_data(rng_val);
    end

    fork
      m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
      begin
        cfg.clk_rst_vif.wait_clks(20000);
        // Check the recov_alert_sts register
        csr_rd_check(.ptr(ral.recov_alert_sts.es_main_sm_alert), .compare_value(1'b1));

        // Set the threshold to make health test not to fail
        ral.repcnt_thresholds.fips_thresh.set(16'hfffe);
        ral.repcnt_thresholds.bypass_thresh.set(16'hfffe);
        csr_update(.csr(ral.repcnt_thresholds));
        // Set to normal sequence
        for (int i = 0; i < m_rng_push_seq.num_trans; i++) begin
          rng_val = i % 16;
          cfg.m_rng_agent_cfg.add_h_user_data(rng_val);
        end
        // Reset the sm
        ral.module_enable.set(prim_mubi_pkg::MuBi4False);
        csr_update(.csr(ral.module_enable));
        ral.module_enable.set(prim_mubi_pkg::MuBi4True);
        csr_update(.csr(ral.module_enable));

        cfg.clk_rst_vif.wait_clks(100);
        // Make sure bit is still on
        csr_rd_check(.ptr(ral.recov_alert_sts.es_main_sm_alert), .compare_value(1'b1));

        // Clear the recov_alert_sts register
        csr_wr(.ptr(ral.recov_alert_sts), .value(32'b0));

        cfg.clk_rst_vif.wait_clks(100);
        // Check the recov_alert_sts register
        csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(0));
        // Stop the sequence
        m_rng_push_seq.stop(.hard(0));
        m_rng_push_seq.wait_for_sequence_state(UVM_FINISHED);
      end
    join
  endtask // test_es_main_sm_alert

  task body();
    string        reg_name;
    string        fld_name;
    int           first_index;
    uvm_reg       csr;
    uvm_reg_field fld;

    // Set the fields to invalid values
    ral.conf.threshold_scope.set(cfg.dut_cfg.ht_threshold_scope);
    csr_update(.csr(ral.conf));
    ral.fw_ov_control.fw_ov_mode.set(cfg.dut_cfg.fw_read_enable);
    ral.fw_ov_control.fw_ov_entropy_insert.set(cfg.dut_cfg.fw_over_enable);
    csr_update(.csr(ral.fw_ov_control));

    cfg.clk_rst_vif.wait_clks(100);

    // Check the recov_alert_sts register
    reg_name = "recov_alert_sts";
    fld_name = cfg.dut_cfg.which_invalid_mubi.name();

    first_index = find_index("_", fld_name, "first");

    csr = ral.get_reg_by_name(reg_name);
    fld = csr.get_field_by_name({fld_name.substr(first_index+1, fld_name.len()-1), "_field_alert"});

    exp_recov_alert_sts = 32'b0;
    exp_recov_alert_sts[fld.get_lsb_pos()] = 1;
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(exp_recov_alert_sts));

    cfg.clk_rst_vif.wait_clks(100);

    // write back valid values
    csr_wr(.ptr(ral.module_enable), .value(prim_mubi_pkg::MuBi4False));
    csr_wr(.ptr(ral.entropy_control), .value(8'h55));
    ral.conf.fips_enable.set(prim_mubi_pkg::MuBi4True);
    ral.conf.entropy_data_reg_enable.set(prim_mubi_pkg::MuBi4True);
    ral.conf.threshold_scope.set(prim_mubi_pkg::MuBi4False);
    ral.conf.rng_bit_enable.set(prim_mubi_pkg::MuBi4False);
    csr_update(.csr(ral.conf));
    ral.fw_ov_control.fw_ov_mode.set(prim_mubi_pkg::MuBi4True);
    ral.fw_ov_control.fw_ov_entropy_insert.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.fw_ov_control));

    // Clear recov_alert_sts register
    csr_wr(.ptr(ral.recov_alert_sts), .value(0));

    // Check recov_alert_sts register
    cfg.clk_rst_vif.wait_clks(100);
    csr_rd_check(.ptr(ral.recov_alert_sts), .compare_value(0));

    // Test es_bus_cmp alert
    test_es_bus_cmp_alert();

    // Wait for some time between tests
    cfg.clk_rst_vif.wait_clks(1000);

    // Test es_main_sm alert
    test_es_main_sm_alert();

    // Test es_thresh_cfg_alert
    test_es_thresh_cfg_alert();

    // Turn assertions back on
    cfg.entropy_src_assert_if.assert_on_alert();
  endtask : body

endclass : entropy_src_alert_vseq
