// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package pattgen_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // TODO: consider to have a parameterized class
  parameter uint NUM_PATTGEN_CHANNELS = 2;

  // local types

  // forward declare classes to allow typedefs below
  typedef class pattgen_item;
  typedef class pattgen_agent_cfg;

  // reuse dv_base_sequencer as is with the right parameter set
  typedef dv_base_sequencer #(.ITEM_T(pattgen_item),
                              .CFG_T (pattgen_agent_cfg)) pattgen_sequencer;

  // package sources
  `include "pattgen_item.sv"
  `include "pattgen_agent_cfg.sv"
  `include "pattgen_agent_cov.sv"
  `include "pattgen_monitor.sv"
  `include "pattgen_driver.sv"
  `include "pattgen_agent.sv"

endpackage: pattgen_agent_pkg
