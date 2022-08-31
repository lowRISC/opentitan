// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// MIO Pads connection
// -------------------
//
// In this test, the vseq should assert the designated PAD to wake the device
// up from the sleep/ deep sleep state. The connections between the PADs and
// the interfaces are hard-coded. Refer tb/tb.sv chip_earlgrey_asic
// instantiation.
//
// Two approaches are possible here:
//
// 1. Trigger each interface op connected to the PAD. For instance, GPIO ports
//    [0:11] are connected to [IOA0:IOA8], [IOB0:IOB2]. Then, call
//    cfg.gpio_vif.drive_pin() to assert PADS.
//
// 2. Force the PAD inout port directly. This is easier as it does not require
//    vif function call. Function call may differ for each interface.
//
class chip_sw_sleep_pin_wake_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sleep_pin_wake_vseq)

  `uvm_object_new

  bit [NUM_GPIOS-1:0] gpios_mask = NUM_GPIOS'(1); // GPIO0 drive

  // The detector module to be used (total 8)
  rand bit [7:0] detector_idx[1];

  // Random delay (in ns)
  // - Fast FSM to enter Low power : 18.8 us
  // - Slow FSM to enter Low power : 278.7us
  //
  // delay should cover the edge case
  rand int unsigned exit_delay;

  constraint pinmux_detector_c {detector_idx[0] inside {[8'h0 : 8'h7]};}

  constraint exit_delay_range_c {
    // Distribution
    exit_delay dist {
      [ 15000: 20000] := 10, // trying to hit when Fast FSM enters LP
      [ 20000:270000] := 2,  // Other scenario (in the middle)
      [270000:300000] := 10  // trying to hit when Slow FSM enters LP
    };
  }

  virtual task cpu_init();
    super.cpu_init();

    sw_symbol_backdoor_overwrite("kWakeupSel", detector_idx);
  endtask : cpu_init

  virtual task body();
    super.body();

    cfg.gpio_vif.drive_en(gpios_mask);
    cfg.gpio_vif.drive(~gpios_mask); // 0

    // Wait until we reach the SW test state.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "pinmux_init end")

    // Wait until chip enters low power (sleep or deep sleep).
    `DV_WAIT(
        cfg.sw_logger_vif.printed_log == "Entering low power mode."
    )

    // Wait #exit_delay ns before asserting a PAD
    #(exit_delay * 1ns)

    // Drive the Pin to high
    `uvm_info(`gfn, "Driving a PAD to wake up the chip", UVM_LOW)

    // TODO: Make it randomize
    // currently driving gpio0 only
    cfg.gpio_vif.drive_pin(0, 1'b 1);

  endtask : body

  virtual task post_start();
    super.post_start();
  endtask : post_start

endclass : chip_sw_sleep_pin_wake_vseq
