// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//halt/resume test
class rv_dm_cmderr_halt_resume_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_cmderr_halt_resume_vseq)

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
      csr_wr(.ptr(jtag_dmi_ral.command), .value(data));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      cfg.rv_dm_vif.unavailable <= data;
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_rd(.ptr(jtag_dmi_ral.abstractcs), .value(rdata));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      `DV_CHECK_EQ(4,get_field_val(jtag_dmi_ral.abstractcs.cmderr,rdata));
      cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
    end
  endtask

endclass : rv_dm_cmderr_halt_resume_vseq
