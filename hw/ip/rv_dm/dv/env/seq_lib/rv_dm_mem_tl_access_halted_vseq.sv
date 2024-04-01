// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// HALTED test vseq
class rv_dm_mem_tl_access_halted_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_mem_tl_access_halted_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }

  task body();
    uvm_reg_data_t r_data;
    // Disable unavailable signal to make sure that hart should be in known state. if hart
    // is unavailable then it could not halted.
    cfg.rv_dm_vif.unavailable <= 0;
    repeat ($urandom_range(1, 10)) begin
      // Verify that writing to HALTED results in anyhalted and allhalted to be set.
      request_halt();
      csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(r_data));
      `DV_CHECK_EQ(1, get_field_val(jtag_dmi_ral.dmstatus.anyhalted, r_data))
      `DV_CHECK_EQ(1, get_field_val(jtag_dmi_ral.dmstatus.allhalted, r_data))
      cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
    end
  endtask : body

endclass : rv_dm_mem_tl_access_halted_vseq
