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
  rand jtag_dmi_op_req_e  req_op;
  rand uvm_reg_addr_t     addr;
  rand uvm_reg_data_t     wdata;

  rand jtag_dmi_op_rsp_e  rsp_op;
  rand uvm_reg_data_t     rdata;

  `uvm_object_utils_begin(jtag_dmi_item)
    `uvm_field_enum(jtag_dmi_op_req_e, req_op, UVM_DEFAULT)
    `uvm_field_int (addr,                      UVM_DEFAULT)
    `uvm_field_int (wdata,                     UVM_DEFAULT)
    `uvm_field_enum(jtag_dmi_op_rsp_e, rsp_op, UVM_DEFAULT)
    `uvm_field_int (rdata,                     UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
