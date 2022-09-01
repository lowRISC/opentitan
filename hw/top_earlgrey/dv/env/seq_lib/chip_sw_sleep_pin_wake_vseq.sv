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

  localparam int unsigned NumMioPads = 49;
  localparam string MioPads [NumMioPads] = '{
    "tb.dut.IOA0",  // MIO0
    "tb.dut.IOA1",  // MIO
    "tb.dut.IOA2",  // MIO
    "tb.dut.IOA3",  // MIO
    "tb.dut.IOA4",  // MIO
    "tb.dut.IOA5",  // MIO
    "tb.dut.IOA6",  // MIO
    "tb.dut.IOA7",  // MIO
    "tb.dut.IOA8",  // MIO
    "tb.dut.IOB0",  // MIO
    "tb.dut.IOB1",  // MIO
    "tb.dut.IOB2",  // MIO
    "tb.dut.IOB3",  // MIO
    "tb.dut.IOB4",  // MIO
    "tb.dut.IOB5",  // MIO
    "tb.dut.IOB6",  // MIO
    "tb.dut.IOB7",  // MIO
    "tb.dut.IOB8",  // MIO
    "tb.dut.IOB9",  // MIO
    "tb.dut.IOB10", // MIO
    "tb.dut.IOB11", // MIO
    "tb.dut.IOB12", // MIO
    "tb.dut.IOC0",  // MIO
    "tb.dut.IOC1",  // MIO
    "tb.dut.IOC2",  // MIO
    "tb.dut.IOC3",  // MIO
    "tb.dut.IOC4",  // MIO
    "tb.dut.IOC5",  // MIO
    "tb.dut.IOC6",  // MIO
    "tb.dut.IOC7",  // MIO
    "tb.dut.IOC8",  // MIO
    "tb.dut.IOC9",  // MIO
    "tb.dut.IOC10", // MIO
    "tb.dut.IOC11", // MIO
    "tb.dut.IOC12", // MIO
    "tb.dut.IOR0",  // MIO
    "tb.dut.IOR1",  // MIO
    "tb.dut.IOR2",  // MIO
    "tb.dut.IOR3",  // MIO
    "tb.dut.IOR4",  // MIO
    "tb.dut.IOR5",  // MIO
    "tb.dut.IOR6",  // MIO
    "tb.dut.IOR7",  // MIO
    "tb.dut.IOR8",  // MIO
    "tb.dut.IOR9",  // MIO
    "tb.dut.IOR10", // MIO
    "tb.dut.IOR11", // MIO
    "tb.dut.IOR12", // MIO
    "tb.dut.IOR13"  // MIO48
  };

  // mio0_dio1 and pad_sel values come from SW
  int unsigned mio0_dio1;
  int unsigned pad_sel;

  // The detector module to be used (total 8)
  rand bit [7:0] detector_idx;

  // Random delay (in ns)
  // - Fast FSM to enter Low power : 18.8 us
  // - Slow FSM to enter Low power : 278.7us
  //
  // delay should cover the edge case
  rand int unsigned exit_delay;

  constraint pinmux_detector_c {detector_idx inside {[8'h0 : 8'h7]};}

  constraint exit_delay_range_c {
    // Distribution
    exit_delay dist {
      [ 15000: 20000] := 10, // trying to hit when Fast FSM enters LP
      [ 20000:270000] := 2,  // Other scenario (in the middle)
      [270000:300000] := 10  // trying to hit when Slow FSM enters LP
    };
  }

  virtual task cpu_init();
    bit [7:0] byte_arr [];

    super.cpu_init();

    byte_arr = '{detector_idx};
    sw_symbol_backdoor_overwrite("kWakeupSel", byte_arr);

  endtask : cpu_init

  virtual task body();
    string printed_log;
    super.body();

    // Wait until we reach the SW test state.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "pinmux_init end")

    // TODO: Get the PAD selection result from SW
    //       1. MIO / DIO
    //       2. MIO PAD SEL OR DIO PAD SEL
    @(cfg.sw_logger_vif.printed_log_event);

    printed_log = string'(cfg.sw_logger_vif.printed_log);
    assert (printed_log.substr(0,9) == "Pad Select") ;

    // SW sends a log with chosen mode, pad formatted as below:
    //   Pad Selection: {mio0_dio1} / {pad_sel}
    mio0_dio1 = cfg.sw_logger_vif.printed_arg[0];
    pad_sel   = cfg.sw_logger_vif.printed_arg[1];

    `uvm_info(`gfn, $sformatf("VSEQ: Pad Selection %d / %d", mio0_dio1, pad_sel), UVM_LOW)

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
    `DV_CHECK(uvm_hdl_force(MioPads[0], 1'b1));

  endtask : body

  virtual task post_start();
    super.post_start();
  endtask : post_start

endclass : chip_sw_sleep_pin_wake_vseq
