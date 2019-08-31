// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package jtag_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint JTAG_IRW = 32; // max IR width
  parameter uint JTAG_DRW = 64; // max DR width

  // local types
  // forward declare classes to allow typedefs below
  typedef class jtag_item;
  typedef class jtag_agent_cfg;

  // reuse dv_base_seqeuencer as is with the right parameter set
  typedef dv_base_sequencer #(.ITEM_T     (jtag_item),
                              .CFG_T      (jtag_agent_cfg)) jtag_sequencer;

  // functions

  // package sources
  `include "jtag_item.sv"
  `include "jtag_agent_cfg.sv"
  `include "jtag_agent_cov.sv"
  `include "jtag_driver.sv"
  `include "jtag_monitor.sv"
  `include "jtag_agent.sv"
  `include "jtag_seq_list.sv"

  endpackage: jtag_agent_pkg
