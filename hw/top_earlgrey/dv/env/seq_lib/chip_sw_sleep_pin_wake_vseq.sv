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

  import chip_common_pkg::*;  // chip_io_e

  localparam int unsigned NumMioPads = top_earlgrey_pkg::MioPadCount;
  localparam int unsigned NumDioPads = top_earlgrey_pkg::DioCount;

  localparam chip_io_e MioPads [NumMioPads] = '{
    IoA0,  // MIO2
    IoA1,  // MIO3
    IoA2,  // MIO4
    IoA3,  // MIO5
    IoA4,  // MIO6
    IoA5,  // MIO7
    IoA6,  // MIO8
    IoA7,  // MIO9
    IoA8,  // MIO10
    IoB0,  // MIO11
    IoB1,  // MIO12
    IoB2,  // MIO13
    IoB3,  // MIO14
    IoB4,  // MIO15
    IoB5,  // MIO16
    IoB6,  // MIO17
    IoB7,  // MIO18
    IoB8,  // MIO19
    IoB9,  // MIO20
    IoB10, // MIO21
    IoB11, // MIO22
    IoB12, // MIO23
    IoC0,  // MIO24
    IoC1,  // MIO25
    IoC2,  // MIO26
    IoC3,  // MIO27
    IoC4,  // MIO28
    IoC5,  // MIO29
    IoC6,  // MIO30
    IoC7,  // MIO31
    IoC8,  // MIO32
    IoC9,  // MIO33
    IoC10, // MIO34
    IoC11, // MIO35
    IoC12, // MIO36
    IoR0,  // MIO37
    IoR1,  // MIO38
    IoR2,  // MIO39
    IoR3,  // MIO40
    IoR4,  // MIO41
    IoR5,  // MIO42
    IoR6,  // MIO43
    IoR7,  // MIO44
    IoR10, // MIO45
    IoR11, // MIO46
    IoR12, // MIO47
    IoR13  // MIO48
  };
  localparam chip_io_e DioPads [NumDioPads] = '{
    UsbP,       // DIO 0
    UsbN,       // DIO 1
    SpiHostD0,  // DIO 2
    SpiHostD1,  // DIO 3
    SpiHostD2,  // DIO 4
    SpiHostD3,  // DIO 5
    SpiDevD0,   // DIO 6
    SpiDevD1,   // DIO 7
    SpiDevD2,   // DIO 8
    SpiDevD3,   // DIO 9
    IoR8,       // DIO 10 EC_RST_L
    IoR9,       // DIO 11 FLASH_WP_L
    SpiDevClk,  // DIO 12
    SpiDevCsL,  // DIO 13
    SpiHostClk, // DIO 14
    SpiHostCsL  // DIO 15
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

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);

    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(LcStProd);
  endtask : dut_init

  virtual task cpu_init();
    bit [7:0] byte_arr [];

    super.cpu_init();

    // Turn off Mux
    cfg.chip_vif.enable_flash_ctrl_jtag = 1'b 0;

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

    cfg.chip_vif.disconnect_all_interfaces(.disconnect_default_pulls(1'b 1));
    cfg.chip_vif.ios_if.pins_pd                      = '1;
    cfg.chip_vif.ios_if.pins_pd[SpiHostD3:SpiHostD0] = '1;
    cfg.chip_vif.ios_if.pins_pu[SpiDevCsL]           = 1'b 1;
    cfg.chip_vif.ios_if.pins_pu[UsbP]                = 1'b 1;
    cfg.chip_vif.ios_if.pins_pd[UsbN]                = 1'b 1;

    // Drive selected pad to 0
    if (mio0_dio1) begin
      cfg.chip_vif.ios_if.drive_pin(DioPads[pad_sel], 1'b 0);
    end else begin
      cfg.chip_vif.ios_if.drive_pin(MioPads[pad_sel-2], 1'b 0);
    end

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
      cfg.chip_vif.ios_if.drive_pin(DioPads[pad_sel], 1'b1);
    end else begin
      // MIO drive. First 2 are tie-0, tie-1
      if (pad_sel inside {0, 1}) begin
        `uvm_error(`gfn, "pad_sel valu 0, 1 are not permitted.")
      end else begin
        cfg.chip_vif.ios_if.drive_pin(MioPads[pad_sel-2], 1'b1);
      end
    end

  endtask : body

  virtual task post_start();
    super.post_start();
  endtask : post_start

endclass : chip_sw_sleep_pin_wake_vseq
