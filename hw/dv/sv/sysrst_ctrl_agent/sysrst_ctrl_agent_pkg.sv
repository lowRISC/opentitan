// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package sysrst_ctrl_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // local types
  // forward declare classes to allow typedefs below
  typedef class sysrst_ctrl_item;
  typedef class sysrst_ctrl_agent_cfg;

  // forward declare sequence classes
  typedef class sysrst_ctrl_in_out_passthrough_seq;

  // reuse dv_base_sequencer as is with the right parameter set
  typedef dv_base_sequencer #(.ITEM_T(sysrst_ctrl_item),
                              .CFG_T (sysrst_ctrl_agent_cfg)) sysrst_ctrl_sequencer;

  // functions

  // package sources
  `include "sysrst_ctrl_item.sv"
  `include "sysrst_ctrl_agent_cfg.sv"
  `include "sysrst_ctrl_agent_cov.sv"
  `include "sysrst_ctrl_driver.sv"
  `include "sysrst_ctrl_monitor.sv"
  `include "sysrst_ctrl_agent.sv"
  `include "sysrst_ctrl_seq_list.sv"

endpackage: sysrst_ctrl_agent_pkg
