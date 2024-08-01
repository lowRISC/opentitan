// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// `Timed registers` cannot be guaranteed to change at an exact time, so a certain amount of
// variability must be expected in the timing.
class usbdev_timed_regs extends uvm_object;
  `uvm_object_utils(usbdev_timed_regs)

  `uvm_object_new

  typedef enum {
    TimedIntrState = 0,
    TimedUsbStat,
    TimedInSent,
    TimedWakeEvents,
    // TimedConfigIn0-.. must have contiguous, ascending values.
    TimedConfigIn0,
    TimedConfigIn1,
    TimedConfigIn2,
    TimedConfigIn3,
    TimedConfigIn4,
    TimedConfigIn5,
    TimedConfigIn6,
    TimedConfigIn7,
    TimedConfigIn8,
    TimedConfigIn9,
    TimedConfigIn10,
    TimedConfigIn11
  } timed_reg_e;

  // Access to DUT clock.
  virtual clk_rst_if clk_rst_vif;
  // Access to DUT registers.
  usbdev_reg_block ral;

  timed_reg timed[timed_reg_e];

  // Monotonic, wrapping cycle count; used to detect when expectations have not been met.
  int time_now = 0;

  // Perform a read of the actual DUT register state, for checking against expectations.
  // Note: we perform a backdoor read to avoid impacting the timing of the DUT and DV.
  task read_act_data(timed_reg_e r, output uvm_reg_data_t act_data);
    case (r)
      TimedIntrState:  csr_rd(.ptr(ral.intr_state),   .value(act_data), .backdoor(1));
      TimedUsbStat:    csr_rd(.ptr(ral.usbstat),      .value(act_data), .backdoor(1));
      TimedInSent:     csr_rd(.ptr(ral.in_sent[0]),   .value(act_data), .backdoor(1));
      TimedConfigIn0:  csr_rd(.ptr(ral.configin[0]),  .value(act_data), .backdoor(1));
      TimedConfigIn1:  csr_rd(.ptr(ral.configin[1]),  .value(act_data), .backdoor(1));
      TimedConfigIn2:  csr_rd(.ptr(ral.configin[2]),  .value(act_data), .backdoor(1));
      TimedConfigIn3:  csr_rd(.ptr(ral.configin[3]),  .value(act_data), .backdoor(1));
      TimedConfigIn4:  csr_rd(.ptr(ral.configin[4]),  .value(act_data), .backdoor(1));
      TimedConfigIn5:  csr_rd(.ptr(ral.configin[5]),  .value(act_data), .backdoor(1));
      TimedConfigIn6:  csr_rd(.ptr(ral.configin[6]),  .value(act_data), .backdoor(1));
      TimedConfigIn7:  csr_rd(.ptr(ral.configin[7]),  .value(act_data), .backdoor(1));
      TimedConfigIn8:  csr_rd(.ptr(ral.configin[8]),  .value(act_data), .backdoor(1));
      TimedConfigIn9:  csr_rd(.ptr(ral.configin[9]),  .value(act_data), .backdoor(1));
      TimedConfigIn10: csr_rd(.ptr(ral.configin[10]), .value(act_data), .backdoor(1));
      TimedConfigIn11: csr_rd(.ptr(ral.configin[11]), .value(act_data), .backdoor(1));
      TimedWakeEvents: csr_rd(.ptr(ral.wake_events),  .value(act_data), .backdoor(1));
      default: `uvm_fatal(`gfn, "Invalid/unrecognized register")
    endcase
    `uvm_info(`gfn, $sformatf("Backdoor read of reg %p yielded 0x%0x", r, act_data), UVM_HIGH)
  endtask

  // Add a timed, predicted state change to the list of expectations for the given register.
  function void predict(timed_reg_e r, uvm_reg_data_t prev_data, uvm_reg_data_t new_data);
    `uvm_info(`gfn, $sformatf("Expecting reg %p <= 0x%0x, from 0x%0x (mask 0x%0x), time_now 0x%0x",
                               r, new_data, prev_data, prev_data ^ new_data, time_now), UVM_MEDIUM)
    timed[r].predict(time_now, new_data, prev_data);
  endfunction

  // Check a DUT read from the specified register against any timed expectations.
  function uvm_reg_data_t read(timed_reg_e r, uvm_reg_data_t act_data);
    `uvm_info(`gfn, $sformatf("Producing prediction for %p, act_data 0x%0x", r, act_data),
              UVM_MEDIUM)
    return timed[r].read(time_now, act_data);
  endfunction

  // This process checks every prediction that is made, using backdoor csr_rd in zero time to avoid
  // interfering with actual CSR reads and the timing of the simulation.
  task check_predictions(ref bit under_reset);
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
  endtask

endclass : usbdev_timed_regs
