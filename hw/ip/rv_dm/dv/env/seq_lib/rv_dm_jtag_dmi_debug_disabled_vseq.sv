// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_jtag_dmi_debug_disabled_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_jtag_dmi_debug_disabled_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }

  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }

  task body();
    uvm_reg_data_t rdata;
    repeat ($urandom_range(1, 10)) begin
    csr_wr(.ptr(jtag_dmi_ral.abstractdata[0]), .value('h58743902));
    csr_rd(.ptr(jtag_dmi_ral.abstractdata[0]), .value(rdata));
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
    cfg.rv_dm_vif.lc_hw_debug_en<=lc_ctrl_pkg::Off;
    csr_wr(.ptr(jtag_dmi_ral.abstractdata[0]), .value('h11035662));
    csr_rd(.ptr(jtag_dmi_ral.abstractdata[0]), .value(rdata));
    `DV_CHECK_EQ(rdata, jtag_dmi_ral.abstractdata[0].get_reset());
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
    cfg.m_jtag_agent_cfg.vif.do_trst_n(2);
    cfg.rv_dm_vif.lc_hw_debug_en<=lc_ctrl_pkg::On;
    cfg.clk_rst_vif.wait_clks(5);
    csr_rd(.ptr(jtag_dmi_ral.abstractdata[0]), .value(rdata));
    `DV_CHECK_EQ('h58743902,rdata);
   end

  endtask : body
endclass  : rv_dm_jtag_dmi_debug_disabled_vseq
