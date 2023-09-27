// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//halt/resume/whereto test
class rv_dm_halt_resume_whereto_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_halt_resume_whereto_vseq)

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
      data = $urandom_range(0,31);
      csr_wr(.ptr(jtag_dmi_ral.dmcontrol.haltreq), .value(1));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_wr(.ptr(tl_mem_ral.halted), .value(0));
      csr_wr(.ptr(jtag_dtm_ral.dmi), .value('h5C00021102));
      csr_rd(.ptr(jtag_dmi_ral.abstractcs), .value(rdata));
      `DV_CHECK_EQ(1,get_field_val(jtag_dmi_ral.abstractcs.busy,rdata));
      csr_rd(.ptr(tl_mem_ral.flags[0]), .value(rdata));
      `DV_CHECK_EQ(1,tl_mem_ral.flags[0].get_mirrored_value());
      csr_wr(.ptr(tl_mem_ral.going), .value(0));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_rd(.ptr(jtag_dmi_ral.abstractcs), .value(rdata));
      `DV_CHECK_EQ(1,get_field_val(jtag_dmi_ral.abstractcs.busy,rdata));
      csr_rd(.ptr(tl_mem_ral.whereto), .value(rdata));
      `DV_CHECK_EQ('h380006f,tl_mem_ral.whereto.get_mirrored_value());
      csr_wr(.ptr(tl_mem_ral.halted), .value(0));
      csr_rd(.ptr(jtag_dmi_ral.abstractcs), .value(rdata));
      `DV_CHECK_EQ(0,get_field_val(jtag_dmi_ral.abstractcs.busy,rdata));
      csr_wr(.ptr(jtag_dmi_ral.dmcontrol.haltreq), .value(0));
      csr_wr(.ptr(jtag_dmi_ral.dmcontrol.resumereq), .value(1));
      csr_rd(.ptr(jtag_dmi_ral.abstractcs), .value(rdata));
      `DV_CHECK_EQ(1,get_field_val(jtag_dmi_ral.abstractcs.busy,rdata));
      csr_rd(.ptr(tl_mem_ral.flags[0]), .value(rdata));
      `DV_CHECK_EQ(2,tl_mem_ral.flags[0].get_mirrored_value());
      csr_wr(.ptr(tl_mem_ral.resuming), .value(0));
    end
  endtask

endclass: rv_dm_halt_resume_whereto_vseq
