// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_agent_cfg extends dv_base_agent_cfg;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual jtag_if vif;

  // Extra interface handle that *may* be used by the monitor instead of vif. If this is not null,
  // the agent monitor will track signals from this interface instead of reading from vif.
  virtual jtag_mon_if mon_vif;

  // Event that is triggered when the physical JTAG interface gets connected.
  uvm_event jtag_if_connected;

  // Length of IR register. Update this field based on the actual width used in the design.
  uint ir_len = JTAG_IRW;

  // JTAG debug transport module (DTM) RAL model based off of RISCV spec 0.13.2 (section 6.1.2).
  jtag_dtm_reg_block jtag_dtm_ral;

  // Option to minize Run-Test/Idle duration
  // Current RVDM has hardcoded dtmcs.idle = 1, which requires a single cycle of Run-Test/Idle duration.
  // This knob can bypass default 1 cycle initial delay of 'driver.drive_jtag_req()' task.
  // Use this knob only for the necessary tests.
  bit     min_rti = 0;

  // This JTAG driver expects to control the JTAG interface clock (TCK), which it does by setting
  // tck_en to 0 or 1. If rtc_length is positive, it gives a number of TCK cycles to "run to clear"
  // (where we expect to be in the RunTest/IDLE state) before disabling the clock.
  //
  // This allows safe interactions with things like DMI operations, where we expect CDC to convert
  // between the JTAG clock and a system clock. This only works when TCK is running!
  int unsigned rtc_length = 0;


  `uvm_object_utils_begin(jtag_agent_cfg)
    `uvm_field_object(jtag_dtm_ral, UVM_DEFAULT)
  `uvm_object_utils_end

  function new (string name = "");
    super.new(name);
    jtag_if_connected = new();
    // Create the JTAG DTM RAL.
    jtag_dtm_ral = jtag_dtm_reg_block::type_id::create("jtag_dtm_ral");
    jtag_dtm_ral.build(.base_addr(0), .csr_excl(null));
    jtag_dtm_ral.set_supports_byte_enable(1'b0);
    jtag_dtm_ral.lock_model();
    jtag_dtm_ral.compute_mapped_addr_ranges();
    jtag_dtm_ral.compute_unmapped_addr_ranges();
    // TODO: fix the computation of mapped and unmapped ranges.
  endfunction : new

endclass
