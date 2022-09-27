// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_err_vseq extends flash_ctrl_rw_vseq;
  `uvm_object_utils(flash_ctrl_err_vseq)
  `uvm_object_new

  // This is called from 'run_error_event'
  bit   stop_txn;

  task body();
    int    state_timeout_ns = 100000; // 100us
    fork
       begin
         super.body();
         `JDBG(("number1 end"))
       end
       begin
          run_error_event();
         `JDBG(("number2 end"))
       end
      begin
        fork
          #1ms;
          begin
            forever begin
              cfg.clk_rst_vif.wait_clks(100);
              `JDBG(("assa: host_send:%0d  host_rcvd:%0d outstanding:%0d dbg_sent:%0d  dbg_rcvd:%0d", cfg.otf_host_rd_sent, cfg.otf_host_rd_rcvd, csr_utils_pkg::outstanding_accesses, d_cnt1, d_cnt2))
            end
          end
        join_any
      end
    join
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
         `JDBG(("number3 end"))

  endtask

  virtual task run_error_event(); endtask
endclass
