// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_item extends uvm_sequence_item;

  // random variables

  // Indicates the sizes of IR and DR transactions respectively.
  //
  // In case of host driver, both, IR and DR transactions can be sent from one single object. The
  // jtag_driver checks these values to know which transaction to send. If both of these lengths are
  // non-zero, then the IR is sent, followed by DR. Both must not be set to 0. If one of them is
  // zero, the other one is sent.
  //
  // In case of monitor, only IR or DR item can be captured and written to the analysis port at a
  // time. Depending on what is captured, it sets the length of the 'other' transaction type to 0.
  rand uint ir_len;
  rand uint dr_len;

  rand logic [JTAG_IRW-1:0] ir;
  rand logic [JTAG_DRW-1:0] dr;
  rand logic [JTAG_DRW-1:0] dout;

  // This field is actually immaterial to JTAG protocol. It only serves as an indicator for JTAG DTM
  // CSR reads or writes.
  rand dv_utils_pkg::bus_op_e bus_op;

  // If the same IR was selected earlier, allow the driver to skip resending the IR again. If IR is
  // different than what was sent before, then the new IR is sent.
  rand bit skip_reselected_ir;
  // This field is used to transition TAP FSM to PauseIr state during an active request
  rand uint ir_pause_count;
  // This field is used to transition TAP FSM to PauseDr state during an active request
  rand uint dr_pause_count;
  // This field is used to indicate the CaptureDr cycle on which the
  // pause state is introduced
  rand uint dr_pause_cycle;
  // This field is used to indicate the CaptureIr cycle on which the
  // pause state is introduced
  rand uint ir_pause_cycle;
  // This field is used to enable dummy IR transaction
  rand bit dummy_ir;
  // This field is used to enable dummy DR transaction
  rand bit dummy_dr;
  // This field is used to indicate if IR transaction exit happens via PauseIR state
  rand bit exit_via_pause_ir;
  // This field is used to indicate if DR transaction exit happens via PauseDR state
  rand bit exit_via_pause_dr;
  // This field is used to indicate if at the end of DR transaction FSM moves to RunTestIdle state
  rand bit exit_to_rti_dr;
  // This field is used to reset TAP FSM to TestLogicReset state
  rand bit reset_tap_fsm;

  constraint ir_len_c {
    ir_len <= JTAG_IRW;
  }

  constraint dr_len_c {
    dr_len <= JTAG_DRW;
  }

  constraint exit_to_rti_dr_c {
    soft exit_to_rti_dr == 1;
  }

  constraint reset_tap_fsm_c {
    soft reset_tap_fsm == 0;
  }

  // At least one of them should be non-zero.
  constraint ir_dr_non_zero_c {
    ir_len > 0 || dr_len > 0;
  }

  constraint skip_reselected_ir_c {
    skip_reselected_ir dist {0:/3, 1:/7};
  }

  constraint ir_pause_count_c {
    ir_pause_count dist {0:/80, [1:40]:/ 20};
  }

  constraint dr_pause_count_c {
    dr_pause_count dist {0:/ 80, [1:40]:/ 20};
  }

  constraint dr_pause_cycle_c {
    if (dr_pause_count > 0 && dr_len > 3) {
      dr_pause_cycle inside {[1:dr_len-3]};
    } else {
      dr_pause_cycle == 0;
    }
    solve dr_len before dr_pause_cycle;
    solve dr_pause_count before dr_pause_cycle;
  }

  constraint ir_pause_cycle_c {
    if (ir_pause_count > 0 && ir_len > 3) {
      ir_pause_cycle inside {[1:ir_len-3]};
    } else {
      ir_pause_cycle == 0;
    }
    solve ir_len before ir_pause_cycle;
    solve ir_pause_count before ir_pause_cycle;
  }

  constraint dummy_ir_c {
    dummy_ir dist { 0 := 99, 1 := 1};
  }

  constraint dummy_dr_c {
    soft dummy_dr == 0;
  }

  constraint exit_via_pause_ir_c {
    exit_via_pause_ir dist { 0 := 90, 1 := 10};
  }

  constraint exit_via_pause_dr_c {
    exit_via_pause_dr dist { 0 := 90, 1 := 10};
  }

  `uvm_object_utils_begin(jtag_item)
    `uvm_field_int(ir_len, UVM_DEFAULT)
    `uvm_field_int(dr_len, UVM_DEFAULT)
    `uvm_field_int(ir,     UVM_DEFAULT)
    `uvm_field_int(dr,     UVM_DEFAULT)
    `uvm_field_int(dout,   UVM_DEFAULT)
    `uvm_field_enum(dv_utils_pkg::bus_op_e, bus_op, UVM_DEFAULT)
    `uvm_field_int(skip_reselected_ir, UVM_DEFAULT)
    `uvm_field_int(ir_pause_count, UVM_NOCOMPARE | UVM_DEFAULT)
    `uvm_field_int(dr_pause_count, UVM_NOCOMPARE | UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
