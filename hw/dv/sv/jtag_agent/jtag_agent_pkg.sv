// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package jtag_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import dv_base_reg_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint JTAG_IRW = 32; // max IR width
  parameter uint JTAG_DRW = 64; // max DR width

  typedef enum bit [3:0] {
    JtagResetState,
    JtagIdleState,
    JtagSelectDrState,
    JtagCaptureDrState,
    JtagShiftDrState,
    JtagExit1DrState,
    JtagPauseDrState,
    JtagExit2DrState,
    JtagUpdateDrState,
    JtagSelectIrState,
    JtagCaptureIrState,
    JtagShiftIrState,
    JtagExit1IrState,
    JtagPauseIrState,
    JtagExit2IrState,
    JtagUpdateIrState
  } jtag_fsm_state_e;

  // Forward declare the classes below due to circular dependencies.
  typedef class jtag_item;
  typedef class jtag_agent_cfg;
  typedef class jtag_dtm_reg_block;
  typedef class jtag_dtm_reg_adapter;

  // reuse dv_base_seqeuencer as is with the right parameter set
  typedef dv_base_sequencer #(.ITEM_T (jtag_item),
                              .CFG_T  (jtag_agent_cfg)) jtag_sequencer;

  // package sources
  `include "jtag_item.sv"
  `include "jtag_agent_cfg.sv"
  `include "jtag_agent_cov.sv"
  `include "jtag_driver.sv"
  `include "jtag_monitor.sv"
  `include "jtag_agent.sv"
  `include "jtag_seq_lib.sv"
  `include "jtag_dtm_reg_block.sv"
  `include "jtag_dtm_reg_adapter.sv"

  endpackage: jtag_agent_pkg
