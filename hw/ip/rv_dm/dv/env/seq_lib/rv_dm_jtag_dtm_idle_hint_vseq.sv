// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//rv_dm_jtag_dtm_idle_hint
class rv_dm_jtag_dtm_idle_hint_vseq  extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_jtag_dtm_idle_hint_vseq)

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
     wdata= $urandom_range(0,31);
     csr_rd(.ptr(jtag_dtm_ral.dtmcs), .value(rdata));
     `DV_CHECK_EQ(1,get_field_val(jtag_dtm_ral.dtmcs.idle,rdata))
     cfg.m_jtag_agent_cfg.min_rti = 1;
     //back to back indirect dmi accesses {op,address,data}
     csr_wr(.ptr(jtag_dtm_ral.dmi), .value('h1034563252));
     csr_rd(.ptr(jtag_dtm_ral.dmi), .value(rdata), .blocking(1));
     csr_wr(.ptr(jtag_dtm_ral.dmi), .value('h8034003212));
     csr_rd(.ptr(jtag_dtm_ral.dmi), .value(rdata), .blocking(1));
     csr_wr(.ptr(jtag_dtm_ral.dmi), .value('h5c34003212));
     csr_rd(.ptr(jtag_dtm_ral.dmi), .value(rdata), .blocking(1));
     csr_rd(.ptr(jtag_dtm_ral.dtmcs), .value(rdata));
     `DV_CHECK_EQ(0,get_field_val(jtag_dtm_ral.dtmcs.dmistat,rdata))
  endtask

endclass : rv_dm_jtag_dtm_idle_hint_vseq
