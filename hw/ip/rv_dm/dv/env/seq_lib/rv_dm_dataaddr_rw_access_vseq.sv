// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//Dataaddr_RW_access_Test
class rv_dm_dataaddr_rw_access_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_dataaddr_rw_access_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }
  task write_and_verify(input uvm_object ptr,int idx);
    uvm_reg_data_t data;
    uvm_reg_data_t rdata;
     data = $urandom;
     csr_wr(.ptr(ptr), .value(data));
     cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
     csr_rd(.ptr(jtag_dmi_ral.abstractdata[idx]), .value(rdata));
     cfg.clk_rst_vif.wait_clks($urandom_range(0, 10));
     `DV_CHECK_EQ(rdata,data);
  endtask
  task body();
     write_and_verify(.ptr(tl_mem_ral.dataaddr[0]),.idx(0));
     write_and_verify(.ptr(tl_mem_ral.dataaddr[1]),.idx(1));
  endtask

endclass : rv_dm_dataaddr_rw_access_vseq
