// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_jtag_dtm_hard_reset_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_jtag_dtm_hard_reset_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }

  task body();

      uvm_reg_data_t rdata;
      cfg.rv_dm_vif.scan_rst_n <= 1'b0;
      csr_wr(.ptr(jtag_dtm_ral.dmi), .value('h103257212));
      csr_wr(.ptr(jtag_dtm_ral.dmi.op), .value('h0));
      csr_wr(.ptr(jtag_dtm_ral.dmi.op), .value('h1));
      csr_wr(.ptr(jtag_dtm_ral.dmi.address), .value('h10));
      csr_rd(.ptr(jtag_dtm_ral.dmi), .value(rdata));
      csr_rd(.ptr(jtag_dmi_ral.abstractcs), .value(rdata));
      `DV_CHECK_EQ(1,get_field_val(jtag_dmi_ral.abstractcs.busy,rdata)); //failing at this stage
      cfg.rv_dm_vif.scan_rst_n <= 1'b1;
      //Optional (To check busy response again)
      csr_wr(.ptr(jtag_dtm_ral.dmi.op), .value('h0));
      csr_rd(.ptr(jtag_dmi_ral.abstractcs), .value(rdata));
      `DV_CHECK_EQ(1,get_field_val(jtag_dmi_ral.abstractcs.busy,rdata));
      //Hard reset & read operation
      csr_wr(.ptr(jtag_dtm_ral.dtmcs.dmihardreset), .value(1));
      csr_rd(.ptr(jtag_dmi_ral.abstractdata[0]), .value(rdata));
      `DV_CHECK_EQ('h103257212,rdata);

  endtask : body
 endclass : rv_dm_jtag_dtm_hard_reset_vseq

