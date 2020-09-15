// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rng_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local types
  // forward declare classes to allow typedefs below
  typedef class rng_item;
  typedef class rng_agent_cfg;

  // reuse dv_base_sequencer as is with the right parameter set
  typedef dv_base_sequencer #(.ITEM_T(rng_item),
                              .CFG_T (rng_agent_cfg)) rng_sequencer;

  typedef enum logic [1:0] {
    RAND,
    INCR,
    CONST
  } entropy_type_t;

  // package sources
  `include "rng_item.sv"
  `include "rng_agent_cfg.sv"
  `include "rng_agent_cov.sv"
  `include "rng_driver.sv"
  `include "rng_monitor.sv"
  `include "rng_agent.sv"
  `include "rng_seq_list.sv"

endpackage: rng_agent_pkg
