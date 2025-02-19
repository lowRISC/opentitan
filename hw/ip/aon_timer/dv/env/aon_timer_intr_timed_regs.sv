// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// `Timed registers` cannot be guaranteed to change at an exact time, so a certain amount of
// variability must be expected in the timing.
class aon_timer_intr_timed_regs extends uvm_object;
  `uvm_object_utils(aon_timer_intr_timed_regs)

  extern function new (string name="");

  typedef enum {
    TimedIntrStateWkupExpired = 0,
    TimedIntrStateWdogBark
  } timed_reg_e;

  // Access to DUT clock.
  virtual clk_rst_if clk_rst_vif;
  // Access to DUT registers.
  aon_timer_reg_block ral;

  timed_reg timed[timed_reg_e];

  // Monotonic, wrapping cycle count; used to detect when expectations have not been met.
  // Incremented in 'check_predictions' task
  int time_now = 0;

  // Perform a read of the actual DUT register state, for checking against expectations.
  // Note: we perform a backdoor read to avoid impacting the timing of the DUT and DV.
  extern task read_act_data(timed_reg_e r, output uvm_reg_data_t act_data);
  // Add a timed, predicted state change to the list of expectations for the given register.
  extern function void predict(timed_reg_e r, uvm_reg_data_t prev_data, uvm_reg_data_t new_data);
  // Check a DUT read from the specified register against any timed expectations.
  extern function uvm_reg_data_t read(timed_reg_e r, uvm_reg_data_t act_data);
  // This process runs forever checking every prediction that is made, using backdoor csr_rd in zero
  // time to avoid interfering with actual CSR reads and the timing of the simulation.
  // It also resets the registers if a reset is seen.
  extern task check_predictions(ref bit under_reset);

endclass : aon_timer_intr_timed_regs

function aon_timer_intr_timed_regs::new (string name="");
  super.new(name);
endfunction : new

task aon_timer_intr_timed_regs::read_act_data(timed_reg_e r, output uvm_reg_data_t act_data);
  case (r)
    TimedIntrStateWkupExpired : begin
      csr_rd(.ptr(ral.intr_state.wkup_timer_expired), .value(act_data), .backdoor(1));
    end
    TimedIntrStateWdogBark : begin
      csr_rd(.ptr(ral.intr_state.wdog_timer_bark), .value(act_data), .backdoor(1));
    end
    default: `uvm_fatal(`gfn, "Invalid/unrecognized register")
  endcase
  `uvm_info(`gfn, $sformatf("Backdoor read of reg %p yielded 0x%0x", r, act_data), UVM_HIGH)
endtask : read_act_data

function void aon_timer_intr_timed_regs::predict(timed_reg_e r, uvm_reg_data_t prev_data,
                                                 uvm_reg_data_t new_data);
  `uvm_info(`gfn, $sformatf("Expecting reg %p <= 0x%0x, from 0x%0x (mask 0x%0x), time_now %0d",
                            r, new_data, prev_data, prev_data ^ new_data, time_now), UVM_MEDIUM)

  // The interrupts get predicted on:
  // - neg-edge for counter > threshold predictions and on
  // - pos-edge for intr_state/test predictions.
  // If they occur at the same clock tick there will be two (maybe opposite) predictions at the same
  // time resulting in an error.
  // The RTL prioritises an intr_state/test write over a counter prediction and hence the oldest
  // prediction is removed to model the RTL correctly.
  // The loop below removes the newest prediction before the new one is added.
  foreach(timed[r].fields[i]) begin
    int unsigned max_delay = timed[r].fields[i].max_delay;
    if ((max_delay + time_now) == timed[r].fields[i].pred_q[$].latest_time) begin
      `uvm_info(`gfn, $sformatf({"There's already a predicted interrupt at the same time. ",
                                 "Priority is given to latest prediction. Removing old ",
                                 "prediction (%p)"}, timed[r].fields[i].pred_q[$]), UVM_DEBUG)

      // Popping the last predicted item, since the new prediction from intr_state wins
      void'(timed[r].fields[i].pred_q.pop_back());
    end
  end
  timed[r].predict(time_now, new_data, prev_data);
endfunction : predict

function uvm_reg_data_t aon_timer_intr_timed_regs::read(timed_reg_e r, uvm_reg_data_t act_data);
  `uvm_info(`gfn, $sformatf("Producing prediction for %p, act_data 0x%0x", r, act_data),
            UVM_MEDIUM)
  return timed[r].read(time_now, act_data);
endfunction : read

task aon_timer_intr_timed_regs::check_predictions(ref bit under_reset);
  // Collect the initial values post-reset.
  wait (clk_rst_vif.rst_n === 1'b1);
  forever begin
    timed_reg_e r;
    // Check on every negedge to avoid races with CSR changes
    @(negedge clk_rst_vif.clk);
    time_now++;
    // Check each of the timed registers for expired expectations.
    r = r.first();
    for (int i=0; i < r.num(); i++) begin
      if (under_reset) begin
        `uvm_info(`gfn, $sformatf("Resetting timed register predictions at 0x%0x", time_now),
                  UVM_MEDIUM)
        timed[r].reset();
      end else if (timed[r].preds_pending()) begin
        uvm_reg_data_t act_data;
        // Something is expected to happen to this register field.
        read_act_data(r, act_data);
        timed[r].check_pred(time_now, $sformatf("%p", r), act_data);
      end
      r = r.next();
    end // for (int i=0; i < r.num(); i++)
  end
endtask : check_predictions
