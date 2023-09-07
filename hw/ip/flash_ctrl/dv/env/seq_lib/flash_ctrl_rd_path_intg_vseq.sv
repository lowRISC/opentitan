// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence sends read traffic with error injection
// at the output of read_buffer.
// Read response will trigger fatal_err.storage_err.
class flash_ctrl_rd_path_intg_vseq extends flash_ctrl_legacy_base_vseq;
  `uvm_object_utils(flash_ctrl_rd_path_intg_vseq)
  `uvm_object_new

  task body();
    string path1, path2;
    int    state_timeout_ns = 100000; // 100us

    repeat(5) begin
      flash_op_t host;
      bit [TL_AW-1:0] tl_addr;
      bit             saw_err, completed;
      data_4s_t rdata;

      // Read buffer can be skipped if descramble is not enabled and there is
      // no backlog at the read response pipeline
      // (https://cs.opensource.google/opentitan/opentitan/+/master:
      //  hw/ip/flash_ctrl/rtl/flash_phy_rd.sv;drc=8046c2896fa50aaf3a186a7ce8c0570db9f99eaf;l=481)
      // Enable ecc for all regions
      flash_otf_region_cfg(.scr_mode(OTFCfgTrue), .ecc_mode(OTFCfgTrue));
      cfg.clk_rst_vif.wait_clks(10);
      for (int k = 0; k < 4; k++) begin
        path1 = $sformatf({"tb.dut.u_eflash.gen_flash_cores[0].u_core",
                           ".u_rd.gen_bufs[%0d].u_rd_buf.data_i[35:28]"}, k);
        path2 = $sformatf({"tb.dut.u_eflash.gen_flash_cores[1].u_core",
                           ".u_rd.gen_bufs[%0d].u_rd_buf.data_i[35:28]"}, k);
        `DV_CHECK(uvm_hdl_force(path1, $urandom()))
        `DV_CHECK(uvm_hdl_force(path2, $urandom()))
      end
      cfg.scb_h.expected_alert["fatal_err"].expected = 1;
      cfg.scb_h.expected_alert["fatal_err"].max_delay = 2000;
      cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;

      cfg.scb_h.exp_tl_rsp_intg_err = 1;
      tl_addr[OTFHostId-2:0] = $urandom();
      tl_addr[1:0] = 'h0;
      tl_addr[OTFBankId] = $urandom_range(0, 1);

      for (int i = 0; i < cfg.otf_num_hr; ++i) begin
        bit local_saw_err;
        // fatal_err.phy_storage_err
        tl_access_w_abort(
                          .addr(tl_addr), .write(1'b0), .completed(completed),
                          .saw_err(local_saw_err),
                          .tl_access_timeout_ns(cfg.seq_cfg.erase_timeout_ns),
                          .data(rdata), .check_rsp(1'b0), .blocking(1),
                          .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.flash_ral_name]));
        saw_err |= local_saw_err;

        if ((i % 2)== 1) tl_addr += 4;
      end
      csr_utils_pkg::wait_no_outstanding_access();
      `DV_CHECK_EQ(saw_err, 1)

      // Check fault_status register and err_code register to make sure
      // host read only triggers fault_status.phy_storage_err
      collect_err_cov_status(ral.fault_status);
      csr_rd_check(.ptr(ral.fault_status.phy_storage_err), .compare_value(1));
      csr_rd_check(.ptr(ral.err_code), .compare_value(0));

      `uvm_info(`gfn, "Wait until all drain", UVM_LOW)
      cfg.clk_rst_vif.wait_clks(100);
      `DV_CHECK(uvm_hdl_release(path1))
      `DV_CHECK(uvm_hdl_release(path2))

      // reset for the next round
      cfg.seq_cfg.disable_flash_init = 1;
      cfg.seq_cfg.en_init_keys_seeds = 0;
      apply_reset();
      csr_wr(.ptr(ral.init), .value(1));
      `uvm_info("Test","OTP",UVM_LOW)
      otp_model();
      `DV_SPINWAIT(wait(cfg.flash_ctrl_vif.rd_buf_en == 1);,
                   "Timed out waiting for rd_buf_en",
                   state_timeout_ns)
      cfg.clk_rst_vif.wait_clks(10);
    end

    // disable tlul_err_cnt check
    cfg.tlul_core_obs_cnt = cfg.tlul_core_exp_cnt;
  endtask

endclass
