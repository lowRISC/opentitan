// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_dmi_item extends uvm_sequence_item;

  // JTAG DMI accesses are driven / monitored by writing to JTAG DTM register called DMI. Please see
  // JTAG RISCV debug specification 0.13.2, section 6.1.5 for more details.
  //
  // These fields are declared with larger widths than actually used. The actual widths are defined
  // in the DMI register defined in the spec. The actual width of these fields are design specific.
  // For the sake of simplicity, we just set them wide enough.
  //
  // These represent both, the driven as well as the monitored transaction. Note that at this time,
  // the jtag_dmi_agent is a monitor-only agent.
  rand jtag_dmi_op_t op;
  rand uvm_reg_data_t data;
  rand uvm_reg_data_t addr;

  `uvm_object_utils_begin(jtag_dmi_item)
    `uvm_field_int(op, UVM_DEFAULT)
    `uvm_field_int(data, UVM_DEFAULT)
    `uvm_field_int(addr, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
