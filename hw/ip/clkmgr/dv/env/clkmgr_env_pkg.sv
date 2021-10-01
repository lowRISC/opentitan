// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package clkmgr_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import clkmgr_ral_pkg::*;

  import lc_ctrl_pkg::lc_tx_t;
  import lc_ctrl_pkg::On;
  import lc_ctrl_pkg::Off;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  typedef virtual clkmgr_if clkmgr_vif;
  typedef virtual clk_rst_if clk_rst_vif;

  // parameters
  localparam int NUM_PERI = 4;
  localparam int NUM_TRANS = 5;

  localparam int MainClkHz = 100_000_000;
  localparam int IoClkHz = 96_000_000;
  localparam int UsbClkHz = 48_000_000;
  localparam int AonClkHz = 200_000;
  localparam int FakeAonClkHz = 7_000_000;

  // alerts
  parameter uint NUM_ALERTS = 2;
  parameter string LIST_OF_ALERTS[] = {"recov_fault", "fatal_fault"};

  // types

  // These are ordered per the bits in the recov_err_code register.
  typedef enum int {
    ClkMesrIo,
    ClkMesrIoDiv2,
    ClkMesrIoDiv4,
    ClkMesrMain,
    ClkMesrUsb
  } clk_mesr_e;

  // The enum values for these match the bit order in the CSRs.
  typedef enum int {
    PeriDiv4,
    PeriDiv2,
    PeriIo,
    PeriUsb
  } peri_e;
  typedef enum int {
    TransAes,
    TransHmac,
    TransKmac,
    TransOtbnIoDiv4,
    TransOtbnMain
  } trans_e;

  // Forward class decl to enable cfg to hold a scoreboard handle.
  typedef class clkmgr_scoreboard;

  localparam int ClkInHz[ClkMesrUsb+1] = {IoClkHz, IoClkHz / 2, IoClkHz / 4, MainClkHz, UsbClkHz};

  localparam int ExpectedCounts[ClkMesrUsb+1] = {
    ClkInHz[ClkMesrIo] / AonClkHz - 1,
    ClkInHz[ClkMesrIoDiv2] / AonClkHz - 1,
    ClkInHz[ClkMesrIoDiv4] / AonClkHz - 1,
    ClkInHz[ClkMesrMain] / AonClkHz - 1,
    ClkInHz[ClkMesrUsb] / AonClkHz - 1
  };

  // functions

  // package sources
  `include "clkmgr_env_cfg.sv"
  `include "clkmgr_env_cov.sv"
  `include "clkmgr_virtual_sequencer.sv"
  `include "clkmgr_scoreboard.sv"
  `include "clkmgr_env.sv"
  `include "clkmgr_vseq_list.sv"

endpackage
