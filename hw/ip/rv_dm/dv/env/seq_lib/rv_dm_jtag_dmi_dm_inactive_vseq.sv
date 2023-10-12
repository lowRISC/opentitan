// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//rv_dm_jtag_dmi_dm_inactive_vseq
class rv_dm_jtag_dmi_dm_inactive_vseq extends rv_dm_common_vseq;
  `uvm_object_utils(rv_dm_jtag_dmi_dm_inactive_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }

  task body();
    uvm_reg_data_t wdata;
    uvm_reg_data_t rdata;
    wdata=$urandom_range(0,31);
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.dmactive), .value(0), .blocking(1), .predict(1));
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
    csr_wr(.ptr(jtag_dmi_ral.abstractdata[0]), .value(wdata));
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
    csr_wr(.ptr(jtag_dmi_ral.progbuf[0]), .value(wdata));
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
    csr_wr(.ptr(jtag_dmi_ral.abstractdata[1]), .value(wdata));
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
    csr_wr(.ptr(jtag_dmi_ral.progbuf[1]), .value(wdata));
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
    csr_rd(.ptr(jtag_dmi_ral.abstractdata[0]), .value(rdata));
    `DV_CHECK_EQ(rdata, jtag_dmi_ral.abstractdata[0].get_reset());
    csr_rd(.ptr(jtag_dmi_ral.progbuf[0]), .value(rdata));
    `DV_CHECK_EQ(rdata, jtag_dmi_ral.progbuf[0].get_reset());
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
    csr_rd(.ptr(jtag_dmi_ral.abstractdata[1]), .value(rdata));
    `DV_CHECK_EQ(rdata, jtag_dmi_ral.abstractdata[1].get_reset());
    csr_rd(.ptr(jtag_dmi_ral.progbuf[1]), .value(rdata));
    `DV_CHECK_EQ(rdata, jtag_dmi_ral.progbuf[1].get_reset());
  endtask

endclass : rv_dm_jtag_dmi_dm_inactive_vseq
