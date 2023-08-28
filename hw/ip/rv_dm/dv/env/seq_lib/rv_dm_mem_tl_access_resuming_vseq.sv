// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// RESUMING test vseq
class rv_dm_mem_tl_access_resuming_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_mem_tl_access_resuming_vseq)

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
    repeat ($urandom_range(1, 10)) begin
      wdata = $urandom_range(0, 1);
      // Verify that writing to RESUMING results in anyresumeack and allresumeack to be set,
      //when resumereq bit is set it will clear the anyresumeack and allresumeack.
      csr_wr(.ptr(tl_mem_ral.halted), .value(wdata));
      csr_wr(.ptr(jtag_dmi_ral.dmcontrol.resumereq), .value(wdata));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_wr(.ptr(tl_mem_ral.resuming), .value(wdata));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rdata));
      `DV_CHECK_EQ(!wdata, get_field_val(jtag_dmi_ral.dmstatus.anyresumeack, rdata))
      `DV_CHECK_EQ(!wdata, get_field_val(jtag_dmi_ral.dmstatus.allresumeack, rdata))
      `DV_CHECK_EQ(1, get_field_val(jtag_dmi_ral.dmstatus.anyrunning, rdata))
      `DV_CHECK_EQ(1, get_field_val(jtag_dmi_ral.dmstatus.allrunning, rdata))
      cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
    end
  endtask : body

endclass : rv_dm_mem_tl_access_resuming_vseq
