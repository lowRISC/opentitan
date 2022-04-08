// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs a program, asserting the lc_escalate_en_i at some point during the run.
// Occasionally, it will assert just before or just after.

class otbn_escalate_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_escalate_vseq)

  `uvm_object_new

  task body();
    string       elf_path;
    int unsigned bda_idx;
    bit          go_before, go_during, go_after;

    elf_path = pick_elf_path();
    `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)

    // Pick whether we're going before (5%), during (90%), or after (5%).
    bda_idx = $urandom_range(100);
    go_before = bda_idx < 5;
    go_during = 5 <= bda_idx && bda_idx < 95;
    go_after = 95 <= bda_idx;

    fork
      load_elf(elf_path, .backdoor(1'b0));
      if (go_before) send_escalation_signal(100);
    join

    if (go_before) begin
      // At this point, we've sent our escalation signal already. Wait for the fatal alert to
      // trigger and then return.
      wait_alert_and_reset();
      return;
    end

    if (go_after) begin
      // We want to send the escalation signal after OTBN is finished. Run an operation, send the
      // signal, then wait for the fatal alert.
      run_otbn();
      send_escalation_signal(10);
      wait_alert_and_reset();
      return;
    end

    // This is the interesting case. Start OTBN running. When this task returns, we'll be in the
    // middle of a run.
    start_running_otbn(.check_end_addr(1'b0));

    // Send an escalation signal immediately (the randomisation about where we should strike has
    // already been done inside start_running_otbn())
    send_escalation_signal(1);

    // Wait for an alert to come out before returning
    wait_alert_and_reset();
  endtask

  // Wait between zero and max_cycles clock cycles and then set the escalation signal to enabled.
  // Return immediately if we go into reset.
  task send_escalation_signal(int unsigned max_cycles);
    cfg.escalate_vif.randomize_after_n_clocks($urandom_range(max_cycles), .f_weight(0));
    if (!(cfg.escalate_vif.enable inside {lc_ctrl_pkg::Off, lc_ctrl_pkg::On})) begin
      $assertoff(0, "tb.dut.u_lc_escalate_en_sync.PrimLcSyncCheckTransients_A");
      $assertoff(0, "tb.dut.u_lc_escalate_en_sync.PrimLcSyncCheckTransients0_A");
      $assertoff(0, "tb.dut.u_lc_escalate_en_sync.PrimLcSyncCheckTransients1_A");
    end

  endtask

  // Wait for a fatal alert to come out and retrigger at least once. Then reset the DUT. This is
  // needed at the end of the sequence because otherwise the monitor that sees the re-triggering
  // fatal alert will stop the test from ever finishing.
  task wait_alert_and_reset();
    if(cfg.escalate_vif.enable != lc_ctrl_pkg::Off) begin
      repeat (2) wait_alert_trigger("fatal", .wait_complete(1));
    end

    do_apply_reset = 1'b1;
    dut_init("HARD");
    $asserton(0, "tb.dut.u_lc_escalate_en_sync.PrimLcSyncCheckTransients_A");
    $asserton(0, "tb.dut.u_lc_escalate_en_sync.PrimLcSyncCheckTransients0_A");
    $asserton(0, "tb.dut.u_lc_escalate_en_sync.PrimLcSyncCheckTransients1_A");
  endtask

endclass
