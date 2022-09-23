// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs a program, asserting the lc_escalate_en_i or lc_rma_req_i at some point
// during the run. Occasionally, it will assert just before or just after.

class otbn_escalate_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_escalate_vseq)

  `uvm_object_new

  task body();
    string       elf_path;
    int unsigned bda_idx;
    bit          go_before, go_during, go_after;
    bit          select_rma_req;

    elf_path = pick_elf_path();
    `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)

    // Pick whether we're going to send RMA request or escalation to OTBN.
    select_rma_req = $urandom_range(1);

    // Pick whether we're going before (5%), during (90%), or after (5%).
    bda_idx = $urandom_range(100);
    go_before = bda_idx < 5;
    go_during = 5 <= bda_idx && bda_idx < 95;
    go_after = 95 <= bda_idx;

    fork
      load_elf(elf_path, .backdoor(1'b0));
      if (go_before) send_lc_ctrl_stimulus(100, select_rma_req);
    join

    if (go_before) begin
      // At this point, we've sent our escalation/rma signal already. Wait for the fatal alert to
      // trigger -in the case of an escalation- and then return. Note that if we send a RMA
      // request, we do not necessarily expect a fatal alert but still want to reset in order to
      // re-enable the assertions.
      wait_alert_and_reset();
      return;
    end

    if (go_after) begin
      // We want to send the escalation/RMA signal after OTBN is finished. Run an operation, send
      // the signal, then wait for the fatal alert.
      run_otbn();
      send_lc_ctrl_stimulus(10, select_rma_req);
      wait_alert_and_reset();
      return;
    end

    // This is the interesting case. Start OTBN running. When this task returns, we'll be in the
    // middle of a run.
    start_running_otbn(.check_end_addr(1'b0));

    // Send an escalation/RMA signal immediately (the randomisation about where we should strike
    // has already been done inside start_running_otbn())
    send_lc_ctrl_stimulus(1, select_rma_req);

    // Wait for an alert to come out before returning
    wait_alert_and_reset();
  endtask

  task send_lc_ctrl_stimulus(int unsigned max_cycles, bit select_rma_req);
    if (select_rma_req) begin
      send_rma_request_signal(max_cycles);
    end else begin
      send_escalation_signal(max_cycles);
    end
  endtask

  // Wait between zero and max_cycles clock cycles and then set the escalation signal to enabled.
  // Return immediately if we go into reset.
  task send_escalation_signal(int unsigned max_cycles);
    cfg.escalate_vif.randomize_enable_after_n_clocks($urandom_range(max_cycles), .f_weight(0));
  endtask

  // Wait between zero and max_cycles clock cycles and then set the RMA request signal to enabled.
  // Return immediately if we go into reset.
  task send_rma_request_signal(int unsigned max_cycles);
    cfg.escalate_vif.randomize_rma_req_after_n_clocks($urandom_range(max_cycles), .f_weight(0));
    // Wait for RMA Ack to Rise
    `DV_SPINWAIT_EXIT(
      wait(cfg.escalate_vif.ack == lc_ctrl_pkg::On);,
      cfg.clk_rst_vif.wait_clks(500);,
      "Not getting rma_ack from OTBN for 500 cycles!")
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
  endtask

endclass
