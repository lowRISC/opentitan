// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// `Timed registers` cannot be guaranteed to change at an exact time, so a certain amount of
// variability must be expected in the timing.
class aon_timer_intr_timed_regs extends uvm_object;
  `uvm_object_utils(aon_timer_intr_timed_regs)

//  `uvm_object_new
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
  int time_now = 0;

  extern task read_act_data(timed_reg_e r, output uvm_reg_data_t act_data);
  extern function void predict(timed_reg_e r, uvm_reg_data_t prev_data, uvm_reg_data_t new_data);
  extern function uvm_reg_data_t read(timed_reg_e r, uvm_reg_data_t act_data);
  extern task check_predictions(ref bit under_reset);


endclass : aon_timer_intr_timed_regs

function aon_timer_intr_timed_regs::new (string name="");
  super.new(name);
endfunction : new

// Perform a read of the actual DUT register state, for checking against expectations.
// Note: we perform a backdoor read to avoid impacting the timing of the DUT and DV.
task aon_timer_intr_timed_regs::read_act_data(timed_reg_e r, output uvm_reg_data_t act_data);
  case (r)
    TimedIntrStateWkupExpired : begin
      csr_rd(.ptr(ral.intr_state.wkup_timer_expired),   .value(act_data), .backdoor(1));
    end
    TimedIntrStateWdogBark    : begin
      csr_rd(.ptr(ral.intr_state.wdog_timer_bark),   .value(act_data), .backdoor(1));
    end
    default: `uvm_fatal(`gfn, "Invalid/unrecognized register")
  endcase
  `uvm_info(`gfn, $sformatf("Backdoor read of reg %p yielded 0x%0x", r, act_data), UVM_HIGH)
endtask : read_act_data

// Add a timed, predicted state change to the list of expectations for the given register.
function void aon_timer_intr_timed_regs::predict(timed_reg_e r, uvm_reg_data_t prev_data,
                                                 uvm_reg_data_t new_data);
  `uvm_info(`gfn, $sformatf("Expecting reg %p <= 0x%0x, from 0x%0x (mask 0x%0x), time_now 0x%0x",
                            r, new_data, prev_data, prev_data ^ new_data, time_now), UVM_MEDIUM)
  `uvm_info(`gfn, $sformatf("Expecting reg %p <= 0x%0x, from 0x%0x (mask 0x%0x), time_now %0d",
                            r, new_data, prev_data, prev_data ^ new_data, time_now), UVM_MEDIUM)
  timed[r].predict(time_now, new_data, prev_data);
endfunction : predict

// Check a DUT read from the specified register against any timed expectations.
function uvm_reg_data_t aon_timer_intr_timed_regs::read(timed_reg_e r, uvm_reg_data_t act_data);
  `uvm_info(`gfn, $sformatf("Producing prediction for %p, act_data 0x%0x", r, act_data),
            UVM_MEDIUM)
  return timed[r].read(time_now, act_data);
endfunction : read

// This process checks every prediction that is made, using backdoor csr_rd in zero time to avoid
// interfering with actual CSR reads and the timing of the simulation.
task aon_timer_intr_timed_regs::check_predictions(ref bit under_reset);
  // Collect the initial values post-reset.
  wait (clk_rst_vif.rst_n === 1'b1);
  forever begin
    timed_reg_e r;
    // The checker cannot afford to wait a cycle for the prediction because the CSR change may
    // occur within the current cycle.
    @(negedge clk_rst_vif.clk);
    time_now++;
    // Check each of the timed registers for expired expectations.
    r = r.first();
    forever begin
      if (under_reset) begin
        `uvm_info(`gfn, $sformatf("Resetting timed register predictions at 0x%0x", time_now),
                  UVM_LOW)
        timed[r].reset();
      end else if (timed[r].preds_pending()) begin
        uvm_reg_data_t act_data;
        // Something is expected to happen to this register field.
        read_act_data(r, act_data);
        timed[r].check_pred(time_now, $sformatf("%p", r), act_data);
      end
      if (r == r.last()) break;
      r = r.next();
    end
  end
endtask : check_predictions
