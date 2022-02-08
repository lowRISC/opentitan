// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class lc_ctrl_regwen_during_op_vseq extends lc_ctrl_smoke_vseq;
  `uvm_object_utils(lc_ctrl_regwen_during_op_vseq)

  constraint num_trans_c {num_trans inside {[5 : 10]};}
  `uvm_object_new


  virtual task pre_start();
    super.pre_start();
    // Increase delay for otp token agents
    // This is to give us time to try some reads and writes to
    // transition_regwen locked registers while the transition is in progress
    if (!cfg.jtag_csr) begin  // TL access
      cfg.m_kmac_app_agent_cfg.rsp_delay_min = 3000;
      cfg.m_kmac_app_agent_cfg.rsp_delay_max = 4000;
    end else begin  // JTAG Access - give us some more time for JTAG
      cfg.m_kmac_app_agent_cfg.rsp_delay_min = 10000;
      cfg.m_kmac_app_agent_cfg.rsp_delay_max = 12000;
    end
    cfg.m_kmac_app_agent_cfg.zero_delays = 0;
  endtask

  virtual task sw_transition_req(bit [TL_DW-1:0] next_lc_state, bit [TL_DW*4-1:0] token_val);
    uint max_wait = !cfg.jtag_csr ? 500 : 3000;
    string wait_msg = $sformatf(
        "No OTP program request received - delayed %0d clock cycles instead", max_wait
    );

    `uvm_info(`gfn, "sw_transition_req: started", UVM_MEDIUM)
    fork
      // Run base sw_transition_req
      super.sw_transition_req(next_lc_state, token_val);

      begin : test_regs_process
        uvm_reg_data_t read_val = 0;
        uvm_reg_data_t write_val = 0;
        bit old_en_scb_ral_update_write = cfg.en_scb_ral_update_write;

        // Wait until we are sure the transition has started
        // indicated be an OTP program request or a number of clock cycles
        `DV_SPINWAIT_EXIT(
            while(cfg.m_otp_prog_pull_agent_cfg.vif.req != 1) cfg.clk_rst_vif.wait_clks(1);,
            cfg.clk_rst_vif.wait_clks(max_wait);, wait_msg)

        cfg.clk_rst_vif.wait_clks(100);
        // Read TRANSITION_REGWEN register - should be 0 by now
        csr_rd_check(.ptr(ral.transition_regwen), .compare_value(0));

        // Try some writes / reads
        write_val = $urandom();
        // Disable write predict in scoreboard to prevent RAL being updated
        // by the writes below - we expect these writes to fail in the RTL
        cfg.en_scb_ral_update_write = 0;
        csr_wr(.ptr(ral.transition_ctrl), .value(write_val));
        csr_wr(.ptr(ral.transition_target), .value(write_val));
        csr_wr(.ptr(ral.otp_vendor_test_ctrl), .value(write_val));
        csr_wr(.ptr(ral.transition_token[0]), .value(write_val));
        csr_wr(.ptr(ral.transition_token[1]), .value(write_val));
        csr_wr(.ptr(ral.transition_token[2]), .value(write_val));
        csr_wr(.ptr(ral.transition_token[3]), .value(write_val));
        // restore en_scb_write_predict
        cfg.en_scb_ral_update_write = old_en_scb_ral_update_write;

        // All should read back with the previous values not the values
        // written above
        csr_rd_check(.ptr(ral.transition_ctrl), .compare_value(`gmv(ral.transition_ctrl)));
        csr_rd_check(.ptr(ral.transition_target), .compare_value(`gmv(ral.transition_target)));
        csr_rd_check(.ptr(ral.otp_vendor_test_ctrl),
                     .compare_value(`gmv(ral.otp_vendor_test_ctrl)));
        csr_rd_check(.ptr(ral.transition_token[0]), .compare_value(`gmv(ral.transition_token[0])));
        csr_rd_check(.ptr(ral.transition_token[1]), .compare_value(`gmv(ral.transition_token[1])));
        csr_rd_check(.ptr(ral.transition_token[2]), .compare_value(`gmv(ral.transition_token[2])));
        csr_rd_check(.ptr(ral.transition_token[3]), .compare_value(`gmv(ral.transition_token[3])));

      end : test_regs_process
    join
    `uvm_info(`gfn, "sw_transition_req: finished", UVM_MEDIUM)
  endtask

endclass
