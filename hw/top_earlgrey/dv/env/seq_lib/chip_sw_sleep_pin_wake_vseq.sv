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

  localparam int unsigned NumMioPads = top_earlgrey_pkg::MioPadCount+2;
  localparam int unsigned NumDioPads = top_earlgrey_pkg::DioCount;

  localparam string MioPads [NumMioPads] = '{
    "1'b0", // Not Used
    "1'b1", // Not Used
    "tb.dut.IOA0",  // MIO2
    "tb.dut.IOA1",  // MIO3
    "tb.dut.IOA2",  // MIO4
    "tb.dut.IOA3",  // MIO5
    "tb.dut.IOA4",  // MIO6
    "tb.dut.IOA5",  // MIO7
    "tb.dut.IOA6",  // MIO8
    "tb.dut.IOA7",  // MIO9
    "tb.dut.IOA8",  // MIO10
    "tb.dut.IOB0",  // MIO11
    "tb.dut.IOB1",  // MIO12
    "tb.dut.IOB2",  // MIO13
    "tb.dut.IOB3",  // MIO14
    "tb.dut.IOB4",  // MIO15
    "tb.dut.IOB5",  // MIO16
    "tb.dut.IOB6",  // MIO17
    "tb.dut.IOB7",  // MIO18
    "tb.dut.IOB8",  // MIO19
    "tb.dut.IOB9",  // MIO20
    "tb.dut.IOB10", // MIO21
    "tb.dut.IOB11", // MIO22
    "tb.dut.IOB12", // MIO23
    "tb.dut.IOC0",  // MIO24
    "tb.dut.IOC1",  // MIO25
    "tb.dut.IOC2",  // MIO26
    "tb.dut.IOC3",  // MIO27
    "tb.dut.IOC4",  // MIO28
    "tb.dut.IOC5",  // MIO29
    "tb.dut.IOC6",  // MIO30
    "tb.dut.IOC7",  // MIO31
    "tb.dut.IOC8",  // MIO32
    "tb.dut.IOC9",  // MIO33
    "tb.dut.IOC10", // MIO34
    "tb.dut.IOC11", // MIO35
    "tb.dut.IOC12", // MIO36
    "tb.dut.IOR0",  // MIO37
    "tb.dut.IOR1",  // MIO38
    "tb.dut.IOR2",  // MIO39
    "tb.dut.IOR3",  // MIO40
    "tb.dut.IOR4",  // MIO41
    "tb.dut.IOR5",  // MIO42
    "tb.dut.IOR6",  // MIO43
    "tb.dut.IOR7",  // MIO44
    "tb.dut.IOR10", // MIO45
    "tb.dut.IOR11", // MIO46
    "tb.dut.IOR12", // MIO47
    "tb.dut.IOR13"  // MIO48
  };
  localparam string DioPads [NumDioPads] = '{
    "tb.dut.USB_P",          // DIO 0
    "tb.dut.USB_N",          // DIO 1
    "tb.dut.SPI_HOST_D0",    // DIO 2
    "tb.dut.SPI_HOST_D1",    // DIO 3
    "tb.dut.SPI_HOST_D2",    // DIO 4
    "tb.dut.SPI_HOST_D3",    // DIO 5
    "tb.dut.SPI_DEV_D0",     // DIO 6
    "tb.dut.SPI_DEV_D1",     // DIO 7
    "tb.dut.SPI_DEV_D2",     // DIO 8
    "tb.dut.SPI_DEV_D3",     // DIO 9
    "tb.dut.IOR8",           // DIO 10 EC_RST_L
    "tb.dut.IOR9",           // DIO 11 FLASH_WP_L
    "tb.dut.SPI_DEV_CLK",    // DIO 12
    "tb.dut.SPI_DEV_CS_L",   // DIO 13
    "tb.dut.SPI_HOST_CLK",   // DIO 14
    "tb.dut.SPI_HOST_CS_L"   // DIO 15
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

    // Drive the pin using DPI `uvm_hdl_force()` function
    if (mio0_dio1) begin
      // DIO drive
      `DV_CHECK(uvm_hdl_force(DioPads[pad_sel], 1'b1));
    end else begin
      // MIO drive
      `DV_CHECK(uvm_hdl_force(MioPads[pad_sel], 1'b1));
    end

  endtask : body

  virtual task post_start();
    super.post_start();
  endtask : post_start

endclass : chip_sw_sleep_pin_wake_vseq
