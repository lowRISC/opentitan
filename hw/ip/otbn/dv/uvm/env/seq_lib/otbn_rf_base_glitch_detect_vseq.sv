// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence to verify the countermeasure(s) OTBN.RF_BASE.DATA_REG_SW.GLITCH_DETECT.

class otbn_rf_base_glitch_detect_vseq extends otbn_single_vseq;
  `uvm_object_utils(otbn_rf_base_glitch_detect_vseq)
  `uvm_object_new

  task body();
    do_end_addr_check = 0;
    fork
      begin
        super.body();
      end
      begin
        corrupt_oh_bit();
      end
    join
  endtask: body

  task corrupt_oh_bit();
    bit wr_en;
    bit [11:0] wr_addr;
    bit [5:0] oh_bit;
    bit [31:0] invalid_oh_val;
    bit [31:0] err_val = 32'd1 << 20;
    string wr_en_path;
    string waddr_path;
    string oh_p;

    wr_en_path = "tb.dut.u_otbn_core.u_otbn_rf_base.gen_rf_base_ff.u_otbn_rf_base_inner.wr_en_i";
    waddr_path = "tb.dut.u_otbn_core.u_otbn_rf_base.gen_rf_base_ff.u_otbn_rf_base_inner.wr_addr_i";
    oh_p = "tb.dut.u_otbn_core.u_otbn_rf_base.gen_rf_base_ff.u_otbn_rf_base_inner.we_onehot[31:0]";
    do begin
      @(cfg.clk_rst_vif.cb);
      uvm_hdl_read(wr_en_path, wr_en);
    end while(!wr_en);
    uvm_hdl_read(waddr_path, wr_addr);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(oh_bit, oh_bit != wr_addr;)
    invalid_oh_val[wr_addr] = 1;
    invalid_oh_val[oh_bit] = 1;
    `DV_CHECK_FATAL(uvm_hdl_force(oh_p, invalid_oh_val) == 1);
    @(cfg.clk_rst_vif.cb);
    cfg.model_agent_cfg.vif.otbn_disable_reg_checks();
    cfg.model_agent_cfg.vif.send_err_escalation(err_val);
    wait(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked);
    `DV_CHECK_FATAL(uvm_hdl_release(oh_p) == 1);
    reset_if_locked();
  endtask

endclass : otbn_rf_base_glitch_detect_vseq
