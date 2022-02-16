// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package key_sideload_agent_pkg;
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
  typedef class key_sideload_item;
  typedef class key_sideload_agent_cfg;

  // functions

  // package sources
  `include "key_sideload_item.sv"
  `include "key_sideload_agent_cfg.sv"
  `include "key_sideload_agent_cov.sv"
  `include "key_sideload_driver.sv"
  `include "key_sideload_monitor.sv"
  `include "key_sideload_sequencer.sv"
  `include "key_sideload_seq_list.sv"
  `include "key_sideload_agent.sv"

endpackage: key_sideload_agent_pkg
