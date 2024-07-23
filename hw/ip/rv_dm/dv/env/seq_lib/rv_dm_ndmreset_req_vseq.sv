// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ndmreset_req sequence.Debugger can issue non-debug reset to rest of the system.
// write known value on any csr of all three RAL Models.
// I have written on csrs of two RAL Models as "rv_dm_regs_Ral_Model" has only one register which is 'WO'.

class rv_dm_ndmreset_req_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_ndmreset_req_vseq)
  `uvm_object_new

  // Read the dmstatus register over DMI
  task read_dmstatus(output dmstatus_t value);
    logic [31:0] rdata;
    csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rdata));
    value = dmstatus_t'(rdata);
  endtask

  // Read dmstatus and check that anyunavail and allunavail are asserted
  task check_unavail();
    dmstatus_t dmstatus;
    read_dmstatus(dmstatus);
    `DV_CHECK(dmstatus.anyunavail)
    `DV_CHECK(dmstatus.allunavail)
  endtask

  // Read the value of the ndmreset_pending_q flag.
  task get_ndmreset_pending(output bit rvalue);
    uvm_reg_data_t val;
    string path = "tb.dut.ndmreset_pending_q";

    `DV_CHECK(uvm_hdl_read(path, val));
    rvalue = val[0];
  endtask

  // Check that the ndmreset_pending_q signal in the design has the value we expect.
  task check_ndmreset_pending(bit expected_value);
    bit seen_value;
    get_ndmreset_pending(seen_value);
    `DV_CHECK_EQ(seen_value, expected_value);
  endtask

  // Clear the ndmreset_pending_q flag if it is currently set.
  task clear_pending_ndmreset();
    bit ndmreset_pending;
    get_ndmreset_pending(ndmreset_pending);
    if (!ndmreset_pending) return;

    // If rv_dm currently thinks an ndmreset is pending, it probably means that we're following a
    // vseq that set the ndmreset field in dmcontrol. To clear this, we need to set the ndmreset_ack
    // signal, which happens in response to a reset through rst_lc_ni. We add short waits after
    // changes to rst_lc_ni so that the signal can flow through some synchronisers.
    begin
      cfg.clk_lc_rst_vif.drive_rst_pin(1'b0);
      cfg.clk_rst_vif.wait_clks(8);
      cfg.clk_lc_rst_vif.drive_rst_pin(1'b1);
      cfg.clk_rst_vif.wait_clks(8);
    end

    // This should now have cleared the pending reset flag. Make sure it is clear.
    check_ndmreset_pending(1'b0);
  endtask

  task body();
    // Clear any ndmreset_pending_q signal
    clear_pending_ndmreset();

    // We want to write known values to registers in each RAL (JTAG DMI, debug memory), but choose
    // registers where this won't actually have any effect.
    //
    // We choose:
    //
    //  - JTAG DMI: progbuf[0] (a word of the program buffer)
    //
    //  - Debug memory: dataaddr[0] (a message register used for passing information to/from
    //                  abstract commandcs)
    csr_wr(.ptr(jtag_dmi_ral.progbuf[0]), .value('h12345678));
    csr_wr(.ptr(tl_mem_ral.dataaddr[0]), .value('h87654321));

    // Request an reset of the "rest of the system" by sending writing over DMI to set the ndmreset
    // field in dmcontrol.
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.ndmreset), .value(1));

    // Check that the ndmreset request appears at top-level. Note that we don't assert that it
    // remains high: it will drop again when we disable lc_hw_debug_en below.
    `DV_CHECK(cfg.rv_dm_vif.cb.ndmreset_req)

    // We should also expect to see the ndmreset_pending_q signal go high (tracking the fact that we
    // are in the middle of an ndm reset)
    check_ndmreset_pending(1'b1);

    // Resetting the system would normally drop the rst_ni pin (resetting rv_dm as well). Because
    // this is an "ndm reset", we don't do that. But we *do* expect to see the reset on the
    // auxiliary clk_rst_lc_ni pin.
    cfg.clk_lc_rst_vif.drive_rst_pin(1'b0);

    // Pretend that the "rest of the system" has indeed seen a reset by asserting the unavailable_i
    // input, which means that the hart is powered down.
    cfg.rv_dm_vif.cb.unavailable <= 1;

    // At this point, "normal debug operation" is not going to be available in the chip. Set
    // lc_hw_debug_en to something other than On. But keep pinmux_hw_debug_en equal to On, so that
    // JTAG access to the debug module is maintained.
    lc_hw_debug_en = 1'b0;
    upd_lc_hw_debug_en();

    // Make sure that dmstatus does indeed reflect the unavailable signals.
    check_unavail();

    // This is the end of the "ndmreset request phase". De-assert the request by writing to
    // dmcontrol over DMI again. The ndm_reset_req_o top-level signal should now be low.
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.ndmreset), .value(0));
    `DV_CHECK(!cfg.rv_dm_vif.cb.ndmreset_req)

    // We still expect the ndmreset_pending_q signal to be high at this point. It's job is to track
    // the entire ndm reset and it should only drop when the rest of the system comes out of reset.
    check_ndmreset_pending(1'b1);

    // At this point, we want to mimic the system coming back up. De-assert the clk_lc_rst_vif reset
    // and then drop the unavailable_i signal to show that the CPU is back. Also behave as lc_ctrl
    // and re-enable debug.
    cfg.clk_lc_rst_vif.drive_rst_pin(1'b1);
    cfg.rv_dm_vif.cb.unavailable <= 0;
    lc_hw_debug_en = 1'b1;
    upd_lc_hw_debug_en();

    // Wait a short time to make sure that the lc_hw_debug_en signal change has made it through the
    // synchroniser primitives.
    cfg.clk_rst_vif.wait_clks(8);

    // The ndmreset should have finished. Check that rv_dm doesn't think it's still pending.
    check_ndmreset_pending(1'b0);

    // Also, the debug module should think that the one and only hart has reset. The allhavereset
    // and anyhavereset fields should all be high.
    begin
      uvm_reg_data_t rvalue;
      csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rvalue));
    end
    `DV_CHECK_EQ(`gmv(jtag_dmi_ral.dmstatus.anyhavereset), 1)
    `DV_CHECK_EQ(`gmv(jtag_dmi_ral.dmstatus.allhavereset), 1)

    // Read back progbuf[0] and dataddr[0]. They should still have the values that we wrote earlier
    // because the ndmreset shouldn't have reset any state inside the debug module itself.
    csr_rd_check(.ptr(jtag_dmi_ral.progbuf[0]), .compare_value('h12345678));
    csr_rd_check(.ptr(tl_mem_ral.dataaddr[0]), .compare_value('h87654321));
  endtask : body

endclass : rv_dm_ndmreset_req_vseq
