// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module strobe;

  // Enable TL-UL integrity checker strobing points.
  `define FI_SIM_Z01X

  initial begin
    @(posedge tb.dut.rst_ni)
    // Start FI injection job. For permanent faults, faults are injected
    // at this point. For transient faults, the cycle counter starts from
    // here.
    $fs_inject;
  end

  integer cmp;

  // Compare outputs of the golden and faulty machine. If we detect a mismatch,
  // set the fault status to "observed, not detected" (ON). If the faulty machine
  // produced an invalid value (X/Z), set to "potentially observed, not detected"
  // (PN).
  always@(negedge tb.dut.clk_i) begin
    cmp = $fs_compare(tb.dut.mem_tl_o, tb.dut.prim_tl_o, tb.dut.core_tl_o);
    if (1 == cmp) begin
      // Mismatch beetween the golden and faulty machine.
      $fs_set_status("ON", "tb.dut.mem_tl_o, tb.dut.prim_tl_o, tb.dut.core_tl_o");
    end else if (2 == cmp) begin
      // Faulty machine has a X/Z at the output.
      $fs_set_status("PN", "tb.dut.mem_tl_o, tb.dut.prim_tl_o, tb.dut.core_tl_o");
    end
  end

  // In the previous always block, we have classified the fault as ON or PN. Now
  // check, if one of the countermeasures has detected the fault. Then, set the
  // fault status to "observed detected" (OD) or "potentially observed, detected"
  // (PD). If one of the alert signal is invalid (X/Z), set to "observed, potentially
  // detected" (OP), "potentially observed, potentially detected" (PP), or "not
  // detected, potentially observed" (NP).
  string status;
  always@(negedge tb.dut.clk_i) begin
    #2;
    cmp = $fs_compare(tb.dut.alert_srcs, tb.dut.mem_tl_intg_err, tb.dut.prim_tl_intg_err,
                      tb.dut.core_tl_intg_err, tb.dut.flash_host_rderr);
    status = $fs_get_status();
    if (1 == cmp) begin
      if (status == "ON") begin
        // Mismatch between golden and faulty machine and the alert was triggered.
        $fs_drop_status("OD", {"tb.dut.alert_srcs, tb.dut.mem_tl_intg_err,",
                        "tb.dut.prim_tl_intg_err, tb.dut.core_tl_intg_err,",
                        "tb.dut.flash_host_rderr"});
      end else if (status == "PN") begin
        // Potential mismatch between golden and faulty machine and the alert was triggered.
        $fs_drop_status("PD", {"tb.dut.alert_srcs, tb.dut.mem_tl_intg_err,",
                        "tb.dut.prim_tl_intg_err, tb.dut.core_tl_intg_err,",
                        "tb.dut.flash_host_rderr"});
      end else begin
        // No mismatch between golden and faulty machine but the alert was triggered.
        $fs_set_status("ND", {"tb.dut.alert_srcs, tb.dut.mem_tl_intg_err,",
                        "tb.dut.prim_tl_intg_err, tb.dut.core_tl_intg_err,",
                        "tb.dut.flash_host_rderr"});
      end
    end else if (2 == cmp) begin
      if (status == "ON") begin
        // Mismatch between golden and faulty machine and the alert was potentially triggered.
        $fs_drop_status("OP", {"tb.dut.alert_srcs, tb.dut.mem_tl_intg_err,",
                        "tb.dut.prim_tl_intg_err, tb.dut.core_tl_intg_err,",
                        "tb.dut.flash_host_rderr"});
      end else if (status == "PN") begin
        // Potential mismatch between golden and faulty machine and the alert was potentially
        // triggered.
        $fs_drop_status("PP", {"tb.dut.alert_srcs, tb.dut.mem_tl_intg_err,",
                        "tb.dut.prim_tl_intg_err, tb.dut.core_tl_intg_err,",
                        "tb.dut.flash_host_rderr"});
      end else begin
        // No mismatch between golden and faulty machine but the alert was potentially triggered.
        $fs_set_status("NP", {"tb.dut.alert_srcs, tb.dut.mem_tl_intg_err,",
                        "tb.dut.prim_tl_intg_err, tb.dut.core_tl_intg_err,",
                        "tb.dut.flash_host_rderr"});
      end
    end
  end
endmodule
