// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.
// Used parser: Fallback (regex)


// This is to prevent AscentLint warnings in the generated
// abstract prim wrapper. These warnings occur due to the .*
// use. TODO: we may want to move these inline waivers
// into a separate, generated waiver file for consistency.
//ri lint_check_off OUTPUT_NOT_DRIVEN INPUT_NOT_READ HIER_BRANCH_NOT_READ
module prim_otp
import prim_otp_pkg::*;
#(

  // Native OTP word size. This determines the size_i granule.
  parameter  int Width         = 16,
  parameter  int Depth         = 1024,
  // This determines the maximum number of native words that
  // can be transferred accross the interface in one cycle.
  parameter  int SizeWidth     = 2,
  // Width of the power sequencing signal.
  parameter  int PwrSeqWidth   = 2,
  // Width of vendor-specific test control signal
  parameter  int TestCtrlWidth   = 32,
  parameter  int TestStatusWidth = 32,
  parameter  int TestVectWidth   = 8,
  // Derived parameters
  localparam int AddrWidth     = prim_util_pkg::vbits(Depth),
  localparam int IfWidth       = 2**SizeWidth*Width,
  // VMEM file to initialize the memory with
  parameter      MemInitFile   = "",
  // Vendor test partition offset and size (both in bytes)
  parameter  int VendorTestOffset = 0,
  parameter  int VendorTestSize   = 0

) (
  input                          clk_i,
  input                          rst_ni,
  // Observability
  input ast_pkg::ast_obs_ctrl_t obs_ctrl_i,
  output logic [7:0] otp_obs_o,
  // Macro-specific power sequencing signals to/from AST
  output logic [PwrSeqWidth-1:0] pwr_seq_o,
  input        [PwrSeqWidth-1:0] pwr_seq_h_i,
  // External programming voltage
  inout wire                     ext_voltage_io,
  // Test interfaces
  input        [TestCtrlWidth-1:0]   test_ctrl_i,
  output logic [TestStatusWidth-1:0] test_status_o,
  output logic [TestVectWidth-1:0]   test_vect_o,
  input  tlul_pkg::tl_h2d_t          test_tl_i,
  output tlul_pkg::tl_d2h_t          test_tl_o,
  // Other DFT signals
  input prim_mubi_pkg::mubi4_t   scanmode_i,  // Scan Mode input
  input                          scan_en_i,   // Scan Shift
  input                          scan_rst_ni, // Scan Reset
  // Alert indication (to be connected to alert sender in the instantiating IP)
  output logic                   fatal_alert_o,
  output logic                   recov_alert_o,
  // Ready valid handshake for read/write command
  output logic                   ready_o,
  input                          valid_i,
  // #(Native words)-1, e.g. size == 0 for 1 native word.
  input [SizeWidth-1:0]          size_i,
  // See prim_otp_pkg for the command encoding.
  input  cmd_e                   cmd_i,
  input [AddrWidth-1:0]          addr_i,
  input [IfWidth-1:0]            wdata_i,
  // Response channel
  output logic                   valid_o,
  output logic [IfWidth-1:0]     rdata_o,
  output err_e                   err_o
);

  if (1) begin : gen_generic
    prim_generic_otp #(
      .Depth(Depth),
      .MemInitFile(MemInitFile),
      .PwrSeqWidth(PwrSeqWidth),
      .SizeWidth(SizeWidth),
      .TestCtrlWidth(TestCtrlWidth),
      .TestStatusWidth(TestStatusWidth),
      .TestVectWidth(TestVectWidth),
      .VendorTestOffset(VendorTestOffset),
      .VendorTestSize(VendorTestSize),
      .Width(Width)
    ) u_impl_generic (
      .*
    );

  end

endmodule
//ri lint_check_on OUTPUT_NOT_DRIVEN INPUT_NOT_READ HIER_BRANCH_NOT_READ
