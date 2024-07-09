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

  task body();
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

    // Pretend that the "rest of the system" has indeed gone into reset by asserting the
    // unavailable_i input, which means that the hart is powered down.
    cfg.rv_dm_vif.cb.unavailable <= 1;

    // At this point, "normal debug operation" is not going to be available in the chip. Set
    // lc_hw_debug_en to something other than On. But keep pinmux_hw_debug_en equal to On, so that
    // JTAG access to the debug module is maintained.
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(lc_hw_debug_en, lc_hw_debug_en != lc_ctrl_pkg::On;)
    cfg.rv_dm_vif.lc_hw_debug_en <= lc_hw_debug_en;

    // Make sure that dmstatus does indeed reflect the unavailable signals.
    check_unavail();

    // This is the end of the "ndmreset request phase". De-assert the request by writing to
    // dmcontrol over DMI again. The ndm_reset_req_o top-level signal should now be low.
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.ndmreset), .value(0));
    `DV_CHECK(!cfg.rv_dm_vif.cb.ndmreset_req)

    // At this point, we want to mimic the system coming back up. De-assert the unavailable_i signal
    // to show that the CPU is back. Also behave as lc_ctrl and re-enable debug.
    cfg.rv_dm_vif.cb.unavailable <= 0;
    lc_hw_debug_en = lc_ctrl_pkg::On;
    cfg.rv_dm_vif.lc_hw_debug_en <= lc_hw_debug_en;

    // Read back progbuf[0] and dataddr[0]. They should still have the values that we wrote earlier
    // because the ndmreset shouldn't have reset any state inside the debug module itself.
    csr_rd_check(.ptr(jtag_dmi_ral.progbuf[0]), .compare_value('h12345678));
    csr_rd_check(.ptr(tl_mem_ral.dataaddr[0]), .compare_value('h87654321));
  endtask : body

endclass : rv_dm_ndmreset_req_vseq
