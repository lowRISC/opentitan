// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package otbn_model_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  typedef enum {
    OtbnModelStart,
    OtbnModelDone
  } otbn_model_item_type_e;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  typedef otbn_model_item;
  typedef otbn_model_agent_cfg;
  // driver and sequencer are not used in this agent. Create these dummy components to avoid compile
  // error due to the TLM connection between monitor and sequencer in dv_base_*.
  // Both TLM fifo/port need to use the same item object (otbn_model_item)
  typedef dv_base_sequencer #(otbn_model_item, otbn_model_agent_cfg) otbn_dummy_sequencer;
  typedef dv_base_driver #(otbn_model_item, otbn_model_agent_cfg) otbn_dummy_driver;

  // package sources
  `include "otbn_model_item.sv"

  `include "otbn_model_agent_cfg.sv"
  `include "otbn_model_monitor.sv"
  `include "otbn_model_agent.sv"

endpackage: otbn_model_agent_pkg
