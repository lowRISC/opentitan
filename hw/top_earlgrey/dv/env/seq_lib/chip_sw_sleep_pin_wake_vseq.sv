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

  // Random delay (in ns)
  // - Fast FSM to enter Low power : 18.8 us
  // - Slow FSM to enter Low power : 278.7us
  //
  // delay should cover the edge case
  rand int unsigned exit_delay;
  constraint exit_delay_range_c {
    // Distribution
    exit_delay dist {
      [ 15000: 20000] := 10, // trying to hit when Fast FSM enters LP
      [ 20000:270000] := 2,  // Other scenario (in the middle)
      [270000:300000] := 10  // trying to hit when Slow FSM enters LP
    };
  }

  // SW-randomized values.
  top_earlgrey_pkg::pad_type_e pad_type;
  int unsigned pad_idx;
  logic [DioCount-1:0]  periph_to_dio_oe;
  logic [MioOutCount-1:0]  periph_to_mio_oe;
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
    `DV_CHECK_STREQ(printed_log.substr(0, 9), "Pad Select")

    // SW sends a log with chosen mode, pad formatted as below:
    //   Pad Selection: {pad_type} / {pad_idx}
    pad_type = top_earlgrey_pkg::pad_type_e'(cfg.sw_logger_vif.printed_arg[0]);
    pad_idx  = cfg.sw_logger_vif.printed_arg[1];
    `uvm_info(`gfn, $sformatf("%0s[%0d] is chosen for wakeup", pad_type.name(), pad_idx), UVM_LOW)

    // Enable weak pulls on MIOs as well to avoid assertion errors.
    cfg.chip_vif.disconnect_all_interfaces(.disconnect_default_pulls(0));

    periph_to_dio_oe = '0;
    periph_to_mio_oe = '0;    
    // Disabling output enables for pads so they can be driven on without contradictions.
    void'(cfg.chip_vif.signal_probe_pinmux_periph_to_dio_oe_i(SignalProbeForce, periph_to_dio_oe));
    void'(cfg.chip_vif.signal_probe_pinmux_periph_to_mio_oe_i(SignalProbeForce, periph_to_mio_oe));    
    drive_pad(pad_type, pad_idx, 0);
    `DV_WAIT(cfg.chip_vif.pwrmgr_low_power);
    #(exit_delay * 1ns);
    drive_pad(pad_type, pad_idx, 1);

    // The SW test randomizes between normal and deep sleep. If deep sleep is chosen, the SW reboots
    // after wake up and starts all over again, beginning from the ROM. The ROM requires the SW
    // strap pins to be driven to legal values when it comes online, so we add this logic below.
    // TODO: Find a better way to do this automatically.
    fork
      begin
        `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom)
        // Drive 0 on the pad, so that the mios and sw_straps are identical.
        cfg.chip_vif.mios_if.drive_pin(pad_idx, 0);
        cfg.chip_vif.sw_straps_if.drive(0);
      end
      // On low power exit, the ROM restarts execution. The testbench at some point, drives the SW
      // strap pins again to legal values so that the ROM does not bomb. It may be possible that the
      // pin chosen for wakeup is one of the same pins used for the SW straps. If the sw_straps_if
      // drives those pins at the same time as mios_if, then it will result in X-prop. If we
      // disconnect the mios_if too soon, then it will result in X-prop from the pinmux's (which is
      // in the AON domain) wakeup detection logic. So, we need to disconnect the pin from mios_if
      // at the same time the sw_straps_if is driven.
      if (pad_type == top_earlgrey_pkg::MioPad &&
          pad_idx inside {[top_earlgrey_pkg::MioPadIoc2:top_earlgrey_pkg::MioPadIoc0]}) begin
        @(cfg.chip_vif.sw_straps_if.pins_oe);
        drive_pad(pad_type, pad_idx, 1'bz);
      end
    join_none
  endtask : body

  virtual task post_start();
    super.post_start();
    // If we reached this point, the SW must have disabled the wakeup detection logic. It is now
    // safe to undrive the pad.
    drive_pad(pad_type, pad_idx, 1'bz);
  endtask

  function void drive_pad(top_earlgrey_pkg::pad_type_e pad_type, int unsigned pad_idx, logic value);
    `uvm_info(`gfn, $sformatf("Driving %0s[%0d] to %0b", pad_type.name(), pad_idx, value), UVM_LOW)
    case (pad_type)
      top_earlgrey_pkg::DioPad: begin
        `DV_CHECK(pad_idx inside {[0:top_earlgrey_pkg::DioCount-1]})
        // DIO from the pinmux peripheral side needs to be mapped to the pad side. This mapping is
        // provided by chip_common_pkg::DioToDioPadMap.
        if (value === 1'bz) cfg.chip_vif.dios_if.drive_en_pin(DioToDioPadMap[pad_idx], 0);
        else                cfg.chip_vif.dios_if.drive_pin(DioToDioPadMap[pad_idx], value);
      end
      top_earlgrey_pkg::MioPad: begin
        `DV_CHECK(pad_idx inside {[0:MioPadCount-1]})
        if (value === 1'bz) cfg.chip_vif.mios_if.drive_en_pin(pad_idx, 0);
        else                cfg.chip_vif.mios_if.drive_pin(pad_idx, value);
      end
      default: `uvm_fatal(`gfn, $sformatf("Invalid pad type: %0d", pad_type))
    endcase
  endfunction

endclass : chip_sw_sleep_pin_wake_vseq
