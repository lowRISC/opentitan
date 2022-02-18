// Copyright lowRISC contributors.
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

  constraint ir_len_c {
    ir_len <= JTAG_IRW;
  }

  constraint dr_len_c {
    dr_len <= JTAG_DRW;
  }

  // At least one of them should be non-zero.
  constraint ir_dr_non_zero_c {
    ir_len > 0 || dr_len > 0;
  }

  constraint skip_reselected_ir_c {
    skip_reselected_ir dist {0:/3, 1:/7};
  }

  `uvm_object_utils_begin(jtag_item)
    `uvm_field_int(ir_len, UVM_DEFAULT)
    `uvm_field_int(dr_len, UVM_DEFAULT)
    `uvm_field_int(ir,     UVM_DEFAULT)
    `uvm_field_int(dr,     UVM_DEFAULT)
    `uvm_field_int(dout,   UVM_DEFAULT)
    `uvm_field_enum(dv_utils_pkg::bus_op_e, bus_op, UVM_DEFAULT)
    `uvm_field_int(skip_reselected_ir, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
