// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs a program, asserting the lc_escalate_en_i or lc_rma_req_i at some point
// during the run. Occasionally, it will assert just before or just after.

class otbn_escalate_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_escalate_vseq)

  `uvm_object_new

  typedef enum integer {
    GO_IMMEDIATELY,
    GO_BEFORE,
    GO_DURING,
    GO_SEC_WIPE_STATE,
    GO_AFTER
  } escalate_timing_e;

  task body();
    string                  elf_path;
    bit                     select_rma_req;
    escalate_timing_e       escalate_timing;
    otbn_pkg::otbn_start_stop_state_e start_stop_state_for_escalate;

    elf_path = pick_elf_path();
    `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)

    // Pick whether we're going to send RMA request or escalation to OTBN.
    select_rma_req = $urandom_range(1);

    // Choose when we send the lc_ctrl stimulus
    // Immediate - Within 5 cycles of simulation start and before we run the OTBN program
    // Before - Within 100 cycles of simulation start and before we run the OTBN program
    // During - During the OTBN run
    // Sec Wipe State - When we observe a particular state of the secure wipe process
    // After - After the OTBN run is complete
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(escalate_timing,
      escalate_timing dist {
        GO_IMMEDIATELY     := 15,
        GO_BEFORE          := 15,
        GO_DURING          := 35,
        GO_SEC_WIPE_STATE  := 30,
        GO_AFTER           :=  5
      };
    )

    fork
      load_elf(elf_path, .backdoor(1'b0));
      begin
        if (escalate_timing == GO_IMMEDIATELY) begin
          send_lc_ctrl_stimulus(5, select_rma_req);
        end
        else if (escalate_timing == GO_BEFORE) begin
          send_lc_ctrl_stimulus(100, select_rma_req);
        end
      end
    join

    if (escalate_timing inside {GO_IMMEDIATELY, GO_BEFORE}) begin
      // At this point, we've sent our escalation/rma signal already. Wait for the fatal alert to
      // trigger -in the case of an escalation- and then return. Note that if we send a RMA
      // request, we do not necessarily expect a fatal alert but still want to reset in order to
      // re-enable the assertions.
      wait_alert_and_reset();
      return;
    end

    if (escalate_timing == GO_AFTER) begin
      // We want to send the escalation/RMA signal after OTBN is finished. Run an operation, send
      // the signal, then wait for the fatal alert.
      run_otbn();
      send_lc_ctrl_stimulus(10, select_rma_req);
      wait_alert_and_reset();
      return;
    end


    `uvm_info(`gfn, "Going during", UVM_LOW)

    if (escalate_timing == GO_DURING) begin
      // Start OTBN running. When this task returns, we'll be in the middle of a run.
      start_running_otbn(.check_end_addr(1'b0));
    end else begin // GO_SEC_WIPE_STATE
      // Randomly choose a state of secure wipe to send the stimulus in
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(start_stop_state_for_escalate,
        start_stop_state_for_escalate inside {
          otbn_pkg::OtbnStartStopSecureWipeWdrUrnd,
          otbn_pkg::OtbnStartStopSecureWipeAccModBaseUrnd,
          otbn_pkg::OtbnStartStopSecureWipeAllZero,
          otbn_pkg::OtbnStartStopSecureWipeComplete
        };
      )
      // Start running OTBN and wait for the state to reach the chosen one in parallel. Fork exits
      // only once we've hit the chosen state
      fork
        start_running_otbn(.check_end_addr(1'b0));
        wait (cfg.trace_vif.otbn_start_stop_state == start_stop_state_for_escalate);
      join
    end

    // Send an escalation/RMA signal immediately (the randomisation about where we should strike
    // has already been done inside start_running_otbn() for GO_DURING)
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
