// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_jtag_dtm_hard_reset_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_jtag_dtm_hard_reset_vseq)

  `uvm_object_new

  task body();
    uvm_reg_data_t wdata;
    uvm_reg_data_t rdata1;
    uvm_reg_data_t rdata2;
    repeat ($urandom_range(1, 10)) begin
      wdata = $urandom_range(0,31);
      csr_wr(.ptr(jtag_dmi_ral.abstractdata[0]), .value(wdata));
      csr_wr(.ptr(jtag_dmi_ral.progbuf[0]), .value(wdata));
      csr_rd(.ptr(jtag_dmi_ral.abstractdata[0]), .value(rdata1));
      csr_rd(.ptr(jtag_dmi_ral.progbuf[0]), .value(rdata2));
      `DV_CHECK_EQ(wdata,rdata1);
      `DV_CHECK_EQ(wdata,rdata2);
      csr_wr(.ptr(jtag_dtm_ral.dtmcs.dmihardreset), .value(1));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_rd(.ptr(jtag_dmi_ral.abstractdata[0]), .value(rdata1));
      csr_rd(.ptr(jtag_dmi_ral.progbuf[0]), .value(rdata2));
      `DV_CHECK_EQ(wdata,rdata1);
      `DV_CHECK_EQ(wdata,rdata2);
    end
  endtask : body
endclass : rv_dm_jtag_dtm_hard_reset_vseq
