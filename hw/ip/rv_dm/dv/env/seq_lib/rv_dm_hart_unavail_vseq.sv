// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// hart unavail test vseq
class rv_dm_hart_unavail_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_hart_unavail_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }

  task body();
    uvm_reg_data_t data;
    repeat ($urandom_range(1, 10)) begin
      data = $urandom_range(0, 1);
      cfg.rv_dm_vif.unavailable <= data;
      csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(data));
      `DV_CHECK_EQ(cfg.rv_dm_vif.unavailable,
                   get_field_val(jtag_dmi_ral.dmstatus.anyunavail, data))
      `DV_CHECK_EQ(cfg.rv_dm_vif.unavailable,
                   get_field_val(jtag_dmi_ral.dmstatus.allunavail, data))
      cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
    end
  endtask : body

endclass : rv_dm_hart_unavail_vseq
