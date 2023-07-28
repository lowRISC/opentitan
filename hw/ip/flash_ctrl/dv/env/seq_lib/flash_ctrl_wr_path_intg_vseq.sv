// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence sends write traffic with or without tlul memory
// bus write path error injection.
// This test will trigger fatal_std_err so clear fatal alert at the end of the test by reset.
class flash_ctrl_wr_path_intg_vseq extends flash_ctrl_rw_vseq;
  `uvm_object_utils(flash_ctrl_wr_path_intg_vseq)
  `uvm_object_new

  task body();
    string path = "tb.dut.u_prog_fifo.wdata_i[38]";
    int    state_timeout_ns = 100000; // 100us

    // Don't select a partition defined as read-only
    cfg.seq_cfg.avoid_ro_partitions = 1'b1;

    repeat(5) begin
      flash_otf_region_cfg(.scr_mode(scr_ecc_cfg), .ecc_mode(scr_ecc_cfg));
      `uvm_info(`gfn, "Assert write path err", UVM_LOW)
      `DV_CHECK(uvm_hdl_force(path, 1'b1))
      $assertoff(0, "tb.dut.u_flash_mp.NoReqWhenErr_A");

      // disable tl_rsp error check
      cfg.m_tl_agent_cfg.check_tl_errs = 0;
      cfg.otf_scb_h.mem_mon_off = 1;
      fork
        begin
          uvm_reg_data_t ldata;
          repeat(cfg.otf_num_rw) begin
            `DV_CHECK_RANDOMIZE_FATAL(this)
            ctrl = rand_op;
            bank = rand_op.addr[OTFBankId];

            if (ctrl.partition == FlashPartData) begin
              num = ctrl_num;
            end else begin
              num = ctrl_info_num;
            end

            // Since we force bit 38 to 1, create more than one bus words
            // to make sure data integrity error is created.
            if (fractions < 4) begin
              fractions = 4;
            end
            randcase
              cfg.otf_wr_pct: begin
                cfg.scb_h.expected_alert["fatal_std_err"].expected = 1;
                cfg.scb_h.expected_alert["fatal_std_err"].max_delay = 2000;
                cfg.scb_h.exp_alert_contd["fatal_std_err"] = 10000;

                // prog_err and mp_err
                set_otf_exp_alert("recov_err");
                prog_flash(ctrl, bank, 1, fractions, 1);
              end
              cfg.otf_rd_pct:read_flash(ctrl, bank, num, fractions);
            endcase
          end // repeat (cfg.otf_num_rw)
          // Check std_fault.prog_intg_err,  err_code.prog_err
          collect_err_cov_status(ral.std_fault_status);
          csr_rd_check(.ptr(ral.std_fault_status.prog_intg_err), .compare_value(1));
          csr_rd_check(.ptr(ral.err_code.prog_err), .compare_value(1));
          csr_rd_check(.ptr(ral.op_status.err), .compare_value(1));
          ldata = get_csr_val_with_updated_field(ral.err_code.prog_err, ldata, 1);
          csr_wr(.ptr(ral.err_code), .value(ldata));
          ldata = get_csr_val_with_updated_field(ral.op_status.err, ldata, 0);
          csr_wr(.ptr(ral.op_status), .value(ldata));
        end
        begin
          for (int i = 0; i < cfg.otf_num_hr; ++i) begin
            fork
              send_rand_host_rd();
            join_none
            #0;
          end
          csr_utils_pkg::wait_no_outstanding_access();
        end
      join

      `uvm_info(`gfn, "Wait until all drain", UVM_LOW)
      cfg.clk_rst_vif.wait_clks(100);
      `DV_CHECK(uvm_hdl_release(path))

      cfg.seq_cfg.disable_flash_init = 1;
      cfg.seq_cfg.en_init_keys_seeds = 0;
      apply_reset();
      cfg.otf_scb_h.clear_fifos();
      cfg.otf_scb_h.stop = 1;
      csr_wr(.ptr(ral.init), .value(1));
      `uvm_info("Test","OTP",UVM_LOW)
      otp_model();
      `DV_SPINWAIT(wait(cfg.flash_ctrl_vif.rd_buf_en == 1);,
                   "Timed out waiting for rd_buf_en",
                   state_timeout_ns)
      cfg.clk_rst_vif.wait_clks(10);
      cfg.otf_scb_h.stop = 0;
    end
    // disable tlul_err_cnt check
    cfg.tlul_core_obs_cnt = cfg.tlul_core_exp_cnt;
  endtask

endclass
