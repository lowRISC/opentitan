// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package clkmgr_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import sec_cm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import clkmgr_ral_pkg::*;
  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;

  import lc_ctrl_pkg::lc_tx_t;
  import lc_ctrl_pkg::On;
  import lc_ctrl_pkg::Off;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  typedef virtual clkmgr_if clkmgr_vif;
  typedef virtual clk_rst_if clk_rst_vif;

  // parameters
  parameter int NUM_PERI = 4;
  parameter int NUM_TRANS = 4;

  typedef logic [NUM_PERI-1:0] peri_enables_t;
  typedef logic [NUM_TRANS-1:0] hintables_t;
  typedef mubi4_t [NUM_TRANS-1:0] mubi_hintables_t;
  parameter mubi_hintables_t IdleAllBusy = {NUM_TRANS{prim_mubi_pkg::MuBi4False}};

  parameter int MainClkHz = 100_000_000;
  parameter int IoClkHz = 96_000_000;
  parameter int UsbClkHz = 48_000_000;
  parameter int AonClkHz = 200_000;
  parameter int FakeAonClkHz = 7_000_000;

  // alerts
  parameter uint NUM_ALERTS = 2;
  parameter string LIST_OF_ALERTS[] = {"recov_fault", "fatal_fault"};

  // types

  // Forward class decl to enable cfg to hold a scoreboard handle.
  typedef class clkmgr_scoreboard;

  // The enum values for these match the bit order in the CSRs.
  typedef enum int {
    PeriDiv4,
    PeriDiv2,
    PeriUsb,
    PeriIo
  } peri_e;
  typedef struct packed {
    logic usb_peri_en;
    logic io_peri_en;
    logic io_div2_peri_en;
    logic io_div4_peri_en;
  } clk_enables_t;

  typedef enum int {
    TransAes,
    TransHmac,
    TransKmac,
    TransOtbn
  } trans_e;
  typedef struct packed {
    logic otbn_main;
    logic kmac;
    logic hmac;
    logic aes;
  } clk_hints_t;

  typedef struct {
    logic valid;
    logic slow;
    logic fast;
  } freq_measurement_t;

  // These are ordered per the bits in the recov_err_code register.
  typedef enum int {
    ClkMesrIo,
    ClkMesrIoDiv2,
    ClkMesrIoDiv4,
    ClkMesrMain,
    ClkMesrUsb
  } clk_mesr_e;

  // Mubi test mode
  typedef enum int {
    ClkmgrMubiNone   = 0,
    ClkmgrMubiIdle   = 1,
    ClkmgrMubiLcCtrl = 2,
    ClkmgrMubiLcHand = 3,
    ClkmgrMubiHand   = 4,
    ClkmgrMubiDiv    = 5
  } clkmgr_mubi_e;

  // This is to examine separately the measurement and timeout recoverable error bits.
  typedef logic [ClkMesrUsb:0] recov_bits_t;

  typedef struct packed {
    recov_bits_t timeouts;
    recov_bits_t measures;
    logic shadow_update;
  } clkmgr_recov_err_t;

  // These must be after the declaration of clk_mesr_e for sizing.
  parameter int ClkInHz[ClkMesrUsb+1] = {IoClkHz, IoClkHz / 2, IoClkHz / 4, MainClkHz, UsbClkHz};

  parameter int ExpectedCounts[ClkMesrUsb+1] = {
    ClkInHz[ClkMesrIo] / AonClkHz - 1,
    ClkInHz[ClkMesrIoDiv2] / AonClkHz - 1,
    ClkInHz[ClkMesrIoDiv4] / AonClkHz - 1,
    ClkInHz[ClkMesrMain] / AonClkHz - 1,
    ClkInHz[ClkMesrUsb] / AonClkHz - 1
  };

  // functions
  function automatic void print_hintable(hintables_t tbl);
    foreach (tbl[i]) begin
      `uvm_info("HINTBL", $sformatf("entry%0d : %b", i, tbl[i]), UVM_LOW)
    end
  endfunction : print_hintable

  function automatic void print_mubi_hintable(mubi_hintables_t tbl);
    string val = "INVALID";
    foreach (tbl[i]) begin
      if (tbl[i].name != "") val = tbl[i].name;
      `uvm_info("MUBIHINTBL", $sformatf("entry%0d : %s", i, val), UVM_LOW)
    end
  endfunction : print_mubi_hintable

  // package sources
  `include "clkmgr_env_cfg.sv"
  `include "clkmgr_env_cov.sv"
  `include "clkmgr_virtual_sequencer.sv"
  `include "clkmgr_scoreboard.sv"
  `include "clkmgr_env.sv"
  `include "clkmgr_vseq_list.sv"

endpackage
