// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
//
// Configuration values for DUT input signals
//
//
// This class randomizes values for DUT signal inputs
// and sets constraints on these values.
//
// This class will be instantiated inside otp_ctrl_env_cfg object, and will connect
// to it's otp_ctrl_vif signals and drive them each reset event
//
// The constraints can be hardened and softened as needed in
// closed-source environment.
// In order to override these constraints, please inherit this class
// and set a type override in the closed source environment

class otp_ctrl_ast_inputs_cfg extends uvm_object;
  `uvm_object_utils(otp_ctrl_ast_inputs_cfg);
  `uvm_object_new

  //  Group: Variables
  rand otp_ast_rsp_t        otp_ast_pwr_seq_h;
  rand logic [otp_ctrl_pkg::OtpTestCtrlWidth-1:0] otp_vendor_test_ctrl;
  rand prim_mubi_pkg::mubi4_t scanmode;
  rand logic                scan_en, scan_rst_n;

  //  Group: Constraints
  constraint dut_values_c {
    otp_vendor_test_ctrl == 32'h0;
  }

endclass: otp_ctrl_ast_inputs_cfg
