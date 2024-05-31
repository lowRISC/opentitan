// Copyright lowRISC contributors (OpenTitan project).
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

  // Check that the IDCODE register works as expected.
  //
  // Write an arbitrary value to the register, which should be ignored because this is a read-only
  // register. Then read the value back. We expect to see RV_DM_JTAG_IDCODE, which the testbench has
  // passed to the DUT as the IdcodeValue parameter.
  task check_idcode();
    uvm_reg_data_t data;
    `DV_CHECK_STD_RANDOMIZE_FATAL(data)
    csr_wr(.ptr(jtag_dtm_ral.idcode), .value(data));
    csr_rd(.ptr(jtag_dtm_ral.idcode), .value(data));
    `DV_CHECK_EQ(data, RV_DM_JTAG_IDCODE)
  endtask

  // Check that writing to haltreq controls the debug_req_o output.
  //
  // The haltreq bit is supposed to tell the (only) hart to halt and allow debug. This is
  // implemented in OpenTitan with a debug_req_o signal coming out of rv_dm. Check that it's wired
  // up correctly.
  task check_haltreq();
    uvm_reg_data_t data = $urandom_range(0, 1);
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.haltreq), .value(data));

    // Check immediately that the write has been reflected in the debug_req_o output. There's no
    // need to wait because the write goes through a jtag_dmi_agent, which follows the write
    // operation with a read operation (polling) to check that it was applied.

    `DV_CHECK_EQ(cfg.rv_dm_vif.cb.debug_req, data)
  endtask

  // Check that the ndmreset field controls the ndmreset_req_o output
  //
  // This is analogous to check_haltreq. Here, we expect the ndmreset field in the dmcontrol
  // register to control the ndmreset_req_o output signal.
  task check_ndmreset();
    uvm_reg_data_t data = $urandom_range(0, 1);
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.ndmreset), .value(data));
    `DV_CHECK_EQ(cfg.rv_dm_vif.cb.ndmreset_req, data)
  endtask

  // Verify that the dmstatus[*unavail] field tracks the unavailable_i input.
  task check_unavailable();
    uvm_reg_data_t data = $urandom_range(0, 1);
    cfg.rv_dm_vif.cb.unavailable <= data;
    csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(data));
    `DV_CHECK_EQ(cfg.rv_dm_vif.unavailable,
                 get_field_val(jtag_dmi_ral.dmstatus.anyunavail, data))
    `DV_CHECK_EQ(cfg.rv_dm_vif.unavailable,
                 get_field_val(jtag_dmi_ral.dmstatus.allunavail, data))
  endtask

  // Verify that writing to dmactive causes dmactive output to be set.
  task check_dmactive();
    uvm_reg_data_t data = $urandom_range(0, 1);
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.dmactive), .value(data));

    // Wait for the DMI transaction to make it from the JTAG clock domain to the system clock. This
    // goes through a dmi_cdc module and takes two JTAG clock cycles.
    cfg.jtag_vif.wait_tck(2);

    `DV_CHECK_EQ(cfg.rv_dm_vif.cb.dmactive, data)
  endtask

  task body();
    repeat ($urandom_range(20, 50)) begin
      randcase
        1: check_idcode();
        1: check_haltreq();
        1: check_ndmreset();
        1: check_unavailable();
      endcase
      cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
    end

    repeat ($urandom_range(1, 5)) begin
      check_dmactive();
      cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
    end

  endtask : body

endclass : rv_dm_smoke_vseq
