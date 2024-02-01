// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_monitor #(type ITEM_T = uvm_sequence_item,
                        type REQ_ITEM_T = ITEM_T,
                        type RSP_ITEM_T = ITEM_T,
                        type CFG_T  = dv_base_agent_cfg,
                        type COV_T  = dv_base_agent_cov) extends uvm_monitor;
  `uvm_component_param_utils(dv_base_monitor #(ITEM_T, CFG_T, COV_T))

  CFG_T cfg;
  COV_T cov;

  // Indicates activity on the interface, driven only within the `monitor_ready_to_end()` task.
  protected bit ok_to_end = 1;

  // Used to ensure we run the watchdog exactly once at the end of the run phase. Cleared at start
  // of run phase. Set once watchdog_ok_to_end has been started at the end of the run_phase.
  protected bit phase_ready_to_end_invoked = 0;

  // Analysis port for the collected transfer.
  uvm_analysis_port #(ITEM_T) analysis_port;

  // item will be sent to this port for seq when req phase is done (last is set)
  uvm_analysis_port #(REQ_ITEM_T) req_analysis_port;
  // item will be sent to this port for seq when rsp phase is done (rsp_done is set)
  uvm_analysis_port #(RSP_ITEM_T) rsp_analysis_port;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    analysis_port = new("analysis_port", this);
    req_analysis_port = new("req_analysis_port", this);
    rsp_analysis_port = new("rsp_analysis_port", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    fork
      collect_trans();
    join
  endtask

  // collect transactions forever
  virtual protected task collect_trans();
    `uvm_fatal(`gfn, "this method is not supposed to be called directly!")
  endtask

  // UVM callback which is invoked during phase sequencing.
  virtual function void phase_ready_to_end(uvm_phase phase);
    if (!phase.is(uvm_run_phase::get())) return;
    if (phase_ready_to_end_invoked) return;

    phase_ready_to_end_invoked = 1;
    fork
      monitor_ready_to_end();
      watchdog_ok_to_end(phase);
    join_none
  endfunction

  // Ensures that ok_to_end when asserted, stays asserted for 1 ok_to_end_delay_ns period.
  //
  // If ok_to_end de-asserts before the watchdog expires, it waits for it to assert again
  // and restarts the timer. This ensures that there is sufficient drain time to allow the
  // simulation to end gracefully. It raises and drops the objection at the appropriate times.
  virtual task watchdog_ok_to_end(uvm_phase run_phase);
    bit objection_raised;
    bit watchdog_done;
    uint watchdog_restart_count = 1;

    forever begin
      if (!objection_raised) begin
        `uvm_info(`gfn, "watchdog_ok_to_end: raising objection", UVM_MEDIUM)
        run_phase.raise_objection(this, {`gfn, " objection raised"});
        objection_raised = 1'b1;
      end

      // Start the timer only when ok_to_end is asserted.
      wait (ok_to_end);
      `uvm_info(`gfn, $sformatf("watchdog_ok_to_end: starting the timer (count: %0d)",
                                watchdog_restart_count++), UVM_MEDIUM)
      fork
        begin: isolation_fork
          fork
            begin
              watchdog_done = 1'b0;
              #(cfg.ok_to_end_delay_ns * 1ns);
              watchdog_done = 1'b1;
            end
            wait (!ok_to_end);
          join_any
          disable fork;
        end: isolation_fork
      join

      // If ok_to_end stayed high throughout the watchdog timer expiry, then drop the objection.
      if (ok_to_end && watchdog_done) begin
        `uvm_info(`gfn, "watchdog_ok_to_end: dropping objection", UVM_MEDIUM)
        run_phase.drop_objection(this, {`gfn, " objection dropped"});
        objection_raised = 1'b0;

        // Wait for ok_to_end to de-assert again in future.
        wait (!ok_to_end);
      end
    end
  endtask

  // Asserts/de-asserts ok_to_end to indicate bus activity.
  //
  // This task is invoked in a forked thread within `phase_ready_to_end()`, which is callback
  // invoked by UVM at the end of the phase. The forked thread does not join. Hence, the extended
  // monitor needs to override this function and assert ok_to_end based on the activity on the bus
  // (assert it when idle, de-assert when its not) in a forever loop.
  virtual task monitor_ready_to_end();
  endtask

endclass
