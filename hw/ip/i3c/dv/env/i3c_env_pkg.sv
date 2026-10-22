// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package i3c_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_base_agent_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import i3c_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint   NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[NUM_ALERTS] = {"fatal_fault"};

  // DUT configuration, as instantiated in Earl Grey. The tb uses these to parameterize the DUT.
  parameter uint ClkFreqMhz   = 96;
  parameter uint NumTargets   = 2;
  parameter bit  HalfCycleScl = 1'b1;

  // Number of Virtual Targets that the CSRs describe.
  parameter uint MaxTargets = i3c_reg_pkg::MaxTargets;

  // Frequency of the AON clock, which clocks the reset detector registers.
  parameter uint AonClkFreqKhz = 200;

  // types
  typedef enum int {
    IntrHci  = 0,
    IntrTarg = 1,
    NumI3cIntr
  } i3c_intr_e;

  // Indices of the I3C bus control outputs of the DUT within `bus_ctrl_vif`.
  typedef enum int {
    BusCtrlSdaHkEn   = 0,
    BusCtrlSclHkEn   = 1,
    BusCtrlSdaPuEn   = 2,
    BusCtrlSdaPu     = 3,
    BusCtrlSclPuEn   = 4,
    NumBusCtrl
  } i3c_bus_ctrl_e;

  // Index of each I3C bus line within `board_pullup_vif`.
  typedef enum int {
    BusSda = 0,
    BusScl = 1,
    NumBusLines
  } i3c_bus_line_e;

  typedef virtual pins_if #(.Width(NumBusLines), .PullStrength("Weak")) board_pullup_vif_t;
  typedef virtual pins_if #(NumBusCtrl) bus_ctrl_vif_t;

  // functions

  // Masks of the bits that the Device Address Table (DAT) stores in each word of an entry. The
  // reserved fields of the HCI specification are not stored and read as zero.
  function automatic void get_dat_word_masks(output uvm_reg_data_t masks[$]);
    i3c_pkg::i3c_dat_entry_t entry = '1;
    bit [1:0][TL_DW-1:0]     words;
    entry.reserved0 = '0;
    entry.reserved1 = '0;
    entry.reserved2 = '0;
    words = entry;
    masks = {words[0], words[1]};
  endfunction

  // Masks of the bits that the Device Characteristics Table (DCT) stores in each word of an entry,
  // as for get_dat_word_masks().
  function automatic void get_dct_word_masks(output uvm_reg_data_t masks[$]);
    i3c_pkg::i3c_dct_entry_t entry = '1;
    bit [3:0][TL_DW-1:0]     words;
    entry.reserved0 = '0;
    entry.reserved1 = '0;
    entry.reserved2 = '0;
    words = entry;
    masks = {words[0], words[1], words[2], words[3]};
  endfunction

  // package sources
  `include "i3c_env_cfg.sv"
  `include "i3c_env_cov.sv"
  `include "i3c_virtual_sequencer.sv"
  `include "i3c_scoreboard.sv"
  `include "i3c_env.sv"
  `include "i3c_vseq_list.sv"

endpackage
