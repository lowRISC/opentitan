// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Object to store LC_CTRL parameter values to be sent from TB to environament
class lc_ctrl_parameters_cfg extends uvm_object;
  // LC_CTRL parameters
  // Enable asynchronous transitions on alerts.
  logic           [NUM_ALERTS-1:0] alert_async_on          = {NUM_ALERTS{1'b1}};
  // Idcode value for the JTAG.
  logic           [          31:0] id_code_value           = 32'h00000001;
  // Random netlist constants
  lc_keymgr_div_t                  keymgr_div_invalid      = LcKeymgrDivWidth'(0);
  lc_keymgr_div_t                  keymgr_div_test_dev_rma = LcKeymgrDivWidth'(1);
  lc_keymgr_div_t                  keymgr_div_production   = LcKeymgrDivWidth'(2);
  `uvm_object_utils_begin(lc_ctrl_parameters_cfg)
    `uvm_field_int(alert_async_on, UVM_DEFAULT)
    `uvm_field_int(id_code_value, UVM_DEFAULT)
    `uvm_field_int(keymgr_div_invalid, UVM_DEFAULT)
    `uvm_field_int(keymgr_div_test_dev_rma, UVM_DEFAULT)
    `uvm_field_int(keymgr_div_production, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new
endclass : lc_ctrl_parameters_cfg
