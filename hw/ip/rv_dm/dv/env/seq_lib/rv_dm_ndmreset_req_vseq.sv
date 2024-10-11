// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_ndmreset_req_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_ndmreset_req_vseq)
  `uvm_object_new

  // Read the dmstatus register over DMI
  task read_dmstatus(output dmstatus_t value);
    logic [31:0] rdata;
    csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rdata));
    value = dmstatus_t'(rdata);
  endtask

  // Read dmstatus and check that anyunavail and allunavail are asserted (unless we are in reset, in
  // which case any value is allowed)
  task check_unavail();
    dmstatus_t dmstatus;
    read_dmstatus(dmstatus);
    if (!cfg.clk_rst_vif.rst_n) return;
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

  // Check that the ndmreset_pending_q signal in the design has the value we expect. If we are in
  // reset, this returns immediately.
  task check_ndmreset_pending(bit expected_value);
    bit seen_value;
    get_ndmreset_pending(seen_value);
    if (!cfg.clk_rst_vif.rst_n) return;
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
    // changes to rst_lc_ni so that the signal can flow through some synchronisers. Skip this wait
    // if there is a system reset.
    fork begin : isolation_fork
      fork
        wait (!cfg.clk_rst_vif.rst_n);
        begin
          cfg.clk_lc_rst_vif.drive_rst_pin(1'b0);
          cfg.clk_rst_vif.wait_clks(8);
          cfg.clk_lc_rst_vif.drive_rst_pin(1'b1);
          cfg.clk_rst_vif.wait_clks(8);
        end
      join_any
      disable fork;
    end join
    if (!cfg.clk_rst_vif.rst_n) return;

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

    // If we are in reset, stop immediately. Otherwise, check that the ndmreset request appears at
    // top-level. Note that we don't assert that it remains high: it will drop again when we disable
    // lc_hw_debug_en below.
    if (!cfg.clk_rst_vif.rst_n) return;
    `DV_CHECK(cfg.rv_dm_vif.cb.ndmreset_req)

    // We should also expect to see the ndmreset_pending_q signal go high (tracking the fact that we
    // are in the middle of an ndm reset)
    check_ndmreset_pending(1'b1);

    // Resetting the system would normally drop the rst_ni pin (resetting rv_dm as well). Because
    // this is an "ndm reset", we don't do that. But we *do* expect to see the reset on the
    // auxiliary clk_rst_lc_ni pin.
    cfg.clk_lc_rst_vif.drive_rst_pin(1'b0);

    // This is a bit of a hack to see a particular conditional coverage point in rv_dm.sv. The
    // coverage point wants to see lc_rst_pending_q && !(ndmreset_pending_q && lc_rst_asserted). The
    // lc_rst_pending_q only becomes true after both the other two have been true, so the only
    // simple way to hit the coverage point is to cause lc_rst_asserted to drop again.
    //
    // This means we have to:
    //
    // 1. See the lc_ctrl reset happen (the statement just above this comment).
    // 2. Wait long enough for that reset to be synchronised into lc_rst_asserted and then
    //    lc_reset_pending_q.
    // 3. Stop the reset again.
    // 4. Wait a few cycles for the missing reset to by synchronised into lc_rst_asserted (which
    //    should drop)
    // 5. Finally apply the reset again.
    //
    // This dance (showing a "glitchy LC reset") shouldn't have any other effect.
    cfg.clk_rst_vif.wait_clks(4);
    cfg.clk_lc_rst_vif.drive_rst_pin(1'b1);
    cfg.clk_rst_vif.wait_clks(10);
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

    // If there has been a system reset in this time, exit the vseq.
    if (!cfg.clk_rst_vif.rst_n) return;

    // We still expect the ndmreset_pending_q signal to be high at this point. It's job is to track
    // the entire ndm reset and it should only drop when the rest of the system comes out of reset.
    check_ndmreset_pending(1'b1);

    // At this point, we want to mimic the system coming back up. De-assert the clk_lc_rst_vif reset
    // and then drop the unavailable_i signal to show that the CPU is back. Also behave as lc_ctrl
    // and re-enable debug.
    cfg.clk_lc_rst_vif.drive_rst_pin(1'b1);

    // Debugging should be enabled again (through lc_hw_debug_en), but that will take a short while
    // (as the rest of the system comes up). Wait 16 cycles to represent this, which allows rv_dm to
    // see the state where the de-asserted LC reset signal has been synchronised (4 cycles) but we
    // haven't yet got far enough to allow debug to work again.
    //
    // Also drop the unavailable_i signal to represent the hart coming back.
    cfg.clk_rst_vif.wait_clks(16);
    cfg.rv_dm_vif.cb.unavailable <= 0;
    lc_hw_debug_en = 1'b1;
    upd_lc_hw_debug_en();

    // Wait a short time to make sure that the lc_hw_debug_en signal change has made it through the
    // synchroniser primitives.
    cfg.clk_rst_vif.wait_clks(8);

    // The ndmreset should have finished. Check that rv_dm doesn't think it's still pending.
    check_ndmreset_pending(1'b0);

    // Also, the debug module should think that the one and only hart has reset. The allhavereset
    // and anyhavereset fields should all be high (but we drop out if there has been a system reset
    // in the meantime)
    begin
      uvm_reg_data_t rvalue;
      csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rvalue));
    end
    if (!cfg.clk_rst_vif.rst_n) return;
    `DV_CHECK_EQ(`gmv(jtag_dmi_ral.dmstatus.anyhavereset), 1)
    `DV_CHECK_EQ(`gmv(jtag_dmi_ral.dmstatus.allhavereset), 1)

    // Read back progbuf[0] and dataddr[0]. They should still have the values that we wrote earlier
    // because the ndmreset shouldn't have reset any state inside the debug module itself.
    csr_rd_check(.ptr(jtag_dmi_ral.progbuf[0]), .compare_value('h12345678));
    csr_rd_check(.ptr(tl_mem_ral.dataaddr[0]), .compare_value('h87654321));
  endtask : body

endclass : rv_dm_ndmreset_req_vseq
