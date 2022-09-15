// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence sends read traffic with error injection
// at the output of read_buffer.
// Read response will trigger fatal_err.storage_err.
class flash_ctrl_rd_path_intg_vseq extends flash_ctrl_rw_vseq;
  `uvm_object_utils(flash_ctrl_rd_path_intg_vseq)
  `uvm_object_new

  task body();
    int idx1, idx2;
    string path1, path2;
    int    state_timeout_ns = 100000; // 100us

    repeat(5) begin
      // Enable ecc for all regions
      flash_otf_region_cfg(.scr_mode(scr_ecc_cfg), .ecc_mode(OTFCfgTrue));
      idx1 = $urandom_range(0, 63);
      idx2 = $urandom_range(0, 63);
      path1 = {"tb.dut.u_eflash.gen_flash_cores[0].u_core",
               $sformatf(".u_rd.gen_bufs[0].u_rd_buf.data_i[%0d]", idx1)};
      path2 = {"tb.dut.u_eflash.gen_flash_cores[1].u_core",
               $sformatf(".u_rd.gen_bufs[0].u_rd_buf.data_i[%0d]", idx2)};

      `uvm_info(`gfn, $sformatf("Assert read path err idx1:%0d idx2:%0d", idx1, idx2), UVM_LOW)
      `DV_CHECK(uvm_hdl_force(path1, 1'b0))
      `DV_CHECK(uvm_hdl_force(path2, 1'b0))
      cfg.scb_h.exp_alert["fatal_err"] = 1;
      cfg.scb_h.alert_chk_max_delay["fatal_err"] = 2000;
      cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;

      fork
        begin
          cfg.otf_scb_h.derr_expected = 1;
          repeat(cfg.otf_num_rw) begin
            `DV_CHECK_RANDOMIZE_FATAL(this)
            ctrl = rand_op;
            bank = rand_op.addr[OTFBankId];
            if (ctrl.partition == FlashPartData) begin
              num = ctrl_num;
            end else begin
              num = ctrl_info_num;
            end
            if (fractions < 4) begin
              fractions = 4;
            end
            // recov_err(rd_err)
            // fatal_err.phy_storage_err
            set_otf_exp_alert("recov_err");
            read_flash(ctrl, bank, num, fractions, ,1);
          end
        end
        begin
          flash_op_t host;
          int host_num, host_bank;
          bit [TL_AW-1:0] tl_addr;
          bit             saw_err, completed;
          data_4s_t rdata;

          cfg.scb_h.exp_tl_rsp_intg_err = 1;
          tl_addr[OTFHostId-2:0] = $urandom();
          tl_addr[1:0] = 'h0;
          tl_addr[OTFBankId] = $urandom_range(0, 1);

          for (int i = 0; i < cfg.otf_num_hr; ++i) begin

            fork
              begin
                bit local_saw_err;
                // fatal_err.phy_storage_err
                tl_access_w_abort(
                  .addr(tl_addr), .write(1'b0), .completed(completed),
                  .saw_err(local_saw_err),
                  .tl_access_timeout_ns(cfg.seq_cfg.erase_timeout_ns),
                  .data(rdata), .check_rsp(1'b0), .blocking(1),
                  .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.flash_ral_name]));
                saw_err |= local_saw_err;
              end
            join_none
            #0;
            if ((i % 2)== 1) tl_addr += 4;

          end
          csr_utils_pkg::wait_no_outstanding_access();
          `DV_CHECK_EQ(saw_err, 1)
        end
      join
      `uvm_info(`gfn, "Wait until all drain", UVM_LOW)
      cfg.clk_rst_vif.wait_clks(100);
      `DV_CHECK(uvm_hdl_release(path1))
      `DV_CHECK(uvm_hdl_release(path2))

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
