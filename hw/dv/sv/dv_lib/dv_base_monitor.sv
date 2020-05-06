// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_monitor #(type ITEM_T = uvm_sequence_item,
                        type CFG_T  = dv_base_agent_cfg,
                        type COV_T  = dv_base_agent_cov) extends uvm_monitor;
  `uvm_component_param_utils(dv_base_monitor #(ITEM_T, CFG_T, COV_T))

  CFG_T cfg;
  COV_T cov;

  // extended monitor needs to drive ok_to_end = 0 when bus is busy, set to 1 when it's not busy
  protected bit ok_to_end = 1;

  // make sure at least we add ok_to_end_delay_ns once and invoke monitor_ready_to_end once
  // after enter phase_ready_to_end
  protected bit watchdog_done;

  // Analysis port for the collected transfer.
  uvm_analysis_port #(ITEM_T) analysis_port;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    analysis_port = new("analysis_port", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    fork
      collect_trans(phase);
    join
  endtask

  // collect transactions forever
  virtual protected task collect_trans(uvm_phase phase);
    `uvm_fatal(`gfn, "this method is not supposed to be called directly!")
  endtask

  virtual function void phase_ready_to_end(uvm_phase phase);
    if (phase.is(uvm_run_phase::get())) begin
      if (watchdog_done) fork
          monitor_ready_to_end();
      join_none
      if (!ok_to_end || !watchdog_done) begin
        phase.raise_objection(this, $sformatf("%s objection raised", `gfn));
        `uvm_info(`gfn, $sformatf("Raised objection, because ok_to_end: %0b, watchdog_done: %0b",
                                  ok_to_end, watchdog_done), UVM_MEDIUM)

        fork
          begin
            // wait until ok_to_end is set plus the delay of ok_to_end_delay_ns
            watchdog_ok_to_end();
            phase.drop_objection(this, $sformatf("%s objection dropped", `gfn));
            `uvm_info(`gfn, $sformatf("Dropped objection"), UVM_MEDIUM)
          end
        join_none;
      end
    end
  endfunction

  // This watchdog will wait for ok_to_end_delay_ns while checking for any
  // traffic on the bus during this period.
  // If traffic is seen before ok_to_end_delay_ns, the watchdog will keep
  // repeating this process until the traffic has stopped.
  virtual task watchdog_ok_to_end();
    fork
      begin : isolation_fork
        bit watchdog_reset;

        fork
          forever begin
            // check the bus interface for any traffic. If any, extend timer for one more
            // ok_to_end_delay_ns
            @(ok_to_end or watchdog_reset);
            if (!ok_to_end && !watchdog_reset) watchdog_reset = 1;
          end
          forever begin
            #(cfg.ok_to_end_delay_ns * 1ns);
            if (!watchdog_reset) begin
              break;
            end else begin
              `uvm_info(`gfn, "Resetting phase watchdog timer", UVM_HIGH)
              watchdog_reset = 0;
            end
          end
        join_any;
        disable fork;

        watchdog_done = 1;
      end : isolation_fork
    join
  endtask

  // this task will be invoked as non-blocking thread when phase first enters phase_ready_to_end
  // extended class can override this task to update ok_to_end
  virtual task monitor_ready_to_end();
  endtask
endclass

