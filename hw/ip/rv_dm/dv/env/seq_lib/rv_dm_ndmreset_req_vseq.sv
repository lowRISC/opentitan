// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ndmreset_req sequence.Debugger can issue non-debug reset to rest of the system.
// write known value on any csr of all three RAL Models.
// I have written on csrs of two RAL Models as "rv_dm_regs_Ral_Model" has only one register which is 'WO'.

class rv_dm_ndmreset_req_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_ndmreset_req_vseq)

  `uvm_object_new

  rand lc_ctrl_pkg::lc_tx_t pinmux_hw_debug_en;
  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint pinmux_hw_debug_en_c {
    pinmux_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }

  task body();
    uvm_reg_data_t wdata;
    uvm_reg_data_t rdata;
    wdata = $urandom;
     repeat ($urandom_range(1, 10)) begin
      csr_wr(.ptr(tl_mem_ral.dataaddr[0]), .value('h58743902));
      csr_wr(.ptr(tl_mem_ral.dataaddr[1]), .value('h92110450));
      csr_wr(.ptr(jtag_dmi_ral.progbuf[0]), .value('h58710590));
      csr_wr(.ptr(jtag_dmi_ral.progbuf[1]), .value('h11035662));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_wr(.ptr(jtag_dmi_ral.dmcontrol.ndmreset), .value(1));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_rd(.ptr(jtag_dmi_ral.dmcontrol), .value(rdata));
      `DV_CHECK_EQ(cfg.rv_dm_vif.ndmreset_req,
      get_field_val(jtag_dmi_ral.dmcontrol.ndmreset, rdata))
      cfg.rv_dm_vif.unavailable = 1;
      lc_hw_debug_en = lc_ctrl_pkg::Off;
      csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rdata));
      `DV_CHECK_EQ(cfg.rv_dm_vif.unavailable,
      get_field_val(jtag_dmi_ral.dmstatus.allunavail, rdata))
      csr_wr(.ptr(jtag_dmi_ral.dmcontrol.ndmreset), .value(0));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_rd(.ptr(jtag_dmi_ral.dmcontrol), .value(rdata));
      `DV_CHECK_EQ(cfg.rv_dm_vif.ndmreset_req,
      get_field_val(jtag_dmi_ral.dmcontrol.ndmreset, rdata))
      cfg.clk_rst_vif.wait_clks($urandom_range(1, 1000));
      cfg.rv_dm_vif.unavailable = 0;
      lc_hw_debug_en = lc_ctrl_pkg::On;
      csr_rd(.ptr(jtag_dmi_ral.progbuf[0]), .value(rdata));
      `DV_CHECK_EQ(rdata, 'h58710590)
      csr_rd(.ptr(jtag_dmi_ral.progbuf[1]), .value(rdata));
      `DV_CHECK_EQ(rdata, 'h11035662)
      csr_rd(.ptr(tl_mem_ral.dataaddr[0]), .value(rdata));
      `DV_CHECK_EQ('h58743902, rdata)
      csr_rd(.ptr(tl_mem_ral.dataaddr[1]), .value(rdata));
      `DV_CHECK_EQ('h92110450, rdata)
      end
  endtask : body

endclass : rv_dm_ndmreset_req_vseq
