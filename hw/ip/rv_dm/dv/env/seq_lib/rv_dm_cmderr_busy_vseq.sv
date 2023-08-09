// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class rv_dm_cmderr_busy_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_cmderr_busy_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }
    uvm_reg_data_t data;
    uvm_reg_data_t rdata;
  task body();
    write_chk(.ptr(jtag_dmi_ral.progbuf[0]));
    write_chk(.ptr(jtag_dmi_ral.abstractdata[0]));
    write_chk(.ptr(jtag_dmi_ral.abstractcs));
    write_chk(.ptr(jtag_dmi_ral.abstractauto));
    write_chk(.ptr(jtag_dmi_ral.command));
    read_chk(.ptr(jtag_dmi_ral.progbuf[0]));
    read_chk(.ptr(jtag_dmi_ral.abstractdata[0]));
  endtask
  task write_chk (input uvm_object ptr);
  repeat ($urandom_range(1, 10)) begin
    data = $urandom;
    csr_wr(.ptr(tl_mem_ral.halted), .value(data));
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
    csr_wr(.ptr(jtag_dmi_ral.command), .value(32'h00231000));
    csr_wr(.ptr(ptr), .value(data));
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
    csr_rd(.ptr(jtag_dmi_ral.abstractcs), .value(rdata));
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
    `DV_CHECK_EQ(1,get_field_val(jtag_dmi_ral.abstractcs.cmderr,rdata));
    cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
    end
  endtask
  task read_chk (input uvm_object ptr);
  repeat ($urandom_range(1, 10)) begin
    data = $urandom;
    csr_wr(.ptr(tl_mem_ral.halted), .value(data));
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
    csr_wr(.ptr(jtag_dmi_ral.command), .value(32'h00231000));
    csr_rd(.ptr(ptr), .value(data));
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
    csr_rd(.ptr(jtag_dmi_ral.abstractcs), .value(rdata));
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
    `DV_CHECK_EQ(1,get_field_val(jtag_dmi_ral.abstractcs.cmderr,rdata));
    cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
    end
  endtask

endclass : rv_dm_cmderr_busy_vseq
