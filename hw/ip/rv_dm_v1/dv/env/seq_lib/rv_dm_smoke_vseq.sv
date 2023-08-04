// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class rv_dm_smoke_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_smoke_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }

  task body();
    // Read the JTAG IDCODE register and verify that it matches the expected value.
    uvm_reg_data_t data;
    repeat ($urandom_range(1, 10)) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)
      csr_wr(.ptr(jtag_dtm_ral.idcode), .value(data));
      csr_rd(.ptr(jtag_dtm_ral.idcode), .value(data));
      `DV_CHECK_EQ(data, RV_DM_JTAG_IDCODE)
    end
    repeat ($urandom_range(1, 10)) begin
      data = $urandom_range(0, 1);
      // Verify that writing to haltreq results in debug_req output to be set.
      csr_wr(.ptr(jtag_dmi_ral.dmcontrol.haltreq), .value(data));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      `DV_CHECK_EQ(cfg.rv_dm_vif.debug_req, data)
      cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
    end
    repeat ($urandom_range(1, 10)) begin
      data = $urandom_range(0, 1);
      // Verify that writing to ndmreset results in ndmreset output to be set.
      csr_wr(.ptr(jtag_dmi_ral.dmcontrol.ndmreset), .value(data));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      `DV_CHECK_EQ(cfg.rv_dm_vif.ndmreset_req, data)
      cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
    end
    repeat ($urandom_range(1, 10)) begin
      data = $urandom_range(0, 1);
      // Verify that the dmstatus[*unavail] field tracks the unavailable_i input.
      cfg.rv_dm_vif.unavailable <= data;
      csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(data));
      `DV_CHECK_EQ(cfg.rv_dm_vif.unavailable,
                   get_field_val(jtag_dmi_ral.dmstatus.anyunavail, data))
      `DV_CHECK_EQ(cfg.rv_dm_vif.unavailable,
                   get_field_val(jtag_dmi_ral.dmstatus.allunavail, data))
      cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
    end
    repeat ($urandom_range(1, 10)) begin
      data = $urandom_range(0, 1);
      // Verify that writing to dmactive results in dmactive output to be set.
      csr_wr(.ptr(jtag_dmi_ral.dmcontrol.dmactive), .value(data));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      `DV_CHECK_EQ(cfg.rv_dm_vif.dmactive, data)
      cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
    end
  endtask : body

endclass : rv_dm_smoke_vseq
