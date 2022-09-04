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
    `uvm_info(`gfn, "Assert write path err", UVM_LOW)
    `DV_CHECK(uvm_hdl_force(path, 1'b1))
     $assertoff(0, "tb.dut.u_flash_mp.NoReqWhenErr_A");

    // disable tl_rsp error check
    cfg.m_tl_agent_cfg.check_tl_errs = 0;
    fork
      begin
        repeat(cfg.otf_num_rw) begin
          `DV_CHECK_RANDOMIZE_FATAL(this)
          ctrl = rand_op;
          bank = rand_op.addr[OTFBankId];
          if (ctrl.partition == FlashPartData) begin
            num = ctrl_num;
          end else begin
            num = ctrl_info_num;
          end
          randcase
            cfg.otf_wr_pct: begin
              uvm_reg_data_t ldata;
              cfg.scb_h.exp_alert["fatal_std_err"] = 1;
              cfg.scb_h.alert_chk_max_delay["fatal_std_err"] = 2000;
              cfg.scb_h.exp_alert_contd["fatal_std_err"] = 10000;

              prog_flash(ctrl, bank, 1, fractions, 1);
              // Check std_fault.prog_intg_err,  err_code.prog_err
              csr_rd_check(.ptr(ral.std_fault_status.prog_intg_err), .compare_value(1));
              csr_rd_check(.ptr(ral.err_code.prog_err), .compare_value(1));
              csr_rd_check(.ptr(ral.op_status.err), .compare_value(1));

              ldata = get_csr_val_with_updated_field(ral.err_code.prog_err, ldata, 1);
              csr_wr(.ptr(ral.err_code), .value(ldata));

              ldata = get_csr_val_with_updated_field(ral.op_status.err, ldata, 0);
              csr_wr(.ptr(ral.op_status), .value(ldata));
            end
            cfg.otf_rd_pct:read_flash(ctrl, bank, num, fractions);
          endcase
        end
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
    // disable tlul_err_cnt check
    cfg.tlul_core_obs_cnt = cfg.tlul_core_exp_cnt;
    flash_init_c.constraint_mode(0);
    flash_init = FlashMemInitRandomize;
    apply_reset();
  endtask

endclass
