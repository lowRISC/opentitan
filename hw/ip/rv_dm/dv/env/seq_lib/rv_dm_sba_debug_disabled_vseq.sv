// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_sba_debug_disabled_vseq extends rv_dm_sba_tl_access_vseq;

  `uvm_object_utils(rv_dm_sba_debug_disabled_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }

  task body();
    uvm_reg_data_t     rdata;
    sba_access_err_e   status;
    logic [BUS_DW-1:0] value_q[$];
    logic [BUS_DW-1:0] value_q1[$];
    logic              addr;

    cfg.debugger.sba_write(addr, value_q, status);
    cfg.debugger.sba_read(addr, value_q1, status);
    csr_rd(.ptr(jtag_dmi_ral.sbdata0), .value(rdata));
    `DV_CHECK(jtag_dmi_ral.sbdata0.get_mirrored_value() != 0)
    cfg.rv_dm_vif.cb.lc_hw_debug_en <= get_rand_lc_tx_val(.t_weight(0),.f_weight(1),
                                                          .other_weight(4));

    cfg.debugger.sba_write(addr, value_q, status);
    cfg.debugger.sba_read(addr, value_q1, status);
    csr_rd(.ptr(jtag_dmi_ral.sbdata0), .value(rdata));
    `DV_CHECK_EQ(0, rdata)
  endtask

endclass : rv_dm_sba_debug_disabled_vseq
