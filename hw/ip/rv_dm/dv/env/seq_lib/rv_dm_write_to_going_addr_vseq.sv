// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// GOING test vseq
class rv_dm_write_to_going_addr_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_write_to_going_addr_vseq)

`uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }
  task body();
    uvm_reg_data_t data;
    uvm_reg_data_t rdata;
     repeat ($urandom_range(1, 10)) begin
      data = $urandom_range(0,1);
      cfg.rv_dm_vif.unavailable <= 0;
      csr_wr(.ptr(jtag_dtm_ral.dmi), .value(data));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_wr(.ptr(jtag_dtm_ral.dmi), .value(data));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_wr(.ptr(tl_mem_ral.halted), .value(0));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rdata));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      `DV_CHECK_EQ(1,get_field_val(jtag_dmi_ral.dmstatus.anyhalted,rdata));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_wr(.ptr(tl_mem_ral.going), .value(1));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rdata));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      `DV_CHECK_EQ(1,get_field_val(jtag_dmi_ral.dmstatus.anyrunning,rdata));
      `DV_CHECK_EQ(1,get_field_val(jtag_dmi_ral.dmstatus.allrunning,rdata));
    end
  endtask

endclass: rv_dm_write_to_going_addr_vseq
