// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence triggers prog_failure alert by setting the error bit in otp_program_rsp
// Then check in scb if the alert is triggered correctly
class lc_ctrl_prog_failure_vseq extends lc_ctrl_smoke_vseq;
  `uvm_object_utils(lc_ctrl_prog_failure_vseq)

  `uvm_object_new

  virtual function void configure_vseq();
    this.trans_success_c.constraint_mode(0);
  endfunction

  virtual task body();
    fork
      super.body();
      set_prog_failure();
    join_any
    disable fork;
  endtask

  virtual task post_start();
    super.post_start();
    // trigger dut_init to make sure always on alert is not firing forever
    dut_init();
  endtask

  task set_prog_failure();
    forever begin
      wait(cfg.m_otp_prog_pull_agent_cfg.vif.req == 1);
      if (trans_success) begin
        cfg.lc_ctrl_vif.prog_err = 0;
      end else begin
        cfg.lc_ctrl_vif.prog_err = 1;
      end
      wait (cfg.m_otp_prog_pull_agent_cfg.vif.req == 0);
      cfg.clk_rst_vif.wait_clks(2);
      cfg.lc_ctrl_vif.prog_err = 0;
    end
  endtask

endclass
