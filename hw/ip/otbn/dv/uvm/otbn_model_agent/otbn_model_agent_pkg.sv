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

  // package sources
  `include "otbn_model_item.sv"

  `include "otbn_model_agent_cfg.sv"
  `include "otbn_model_monitor.sv"
  `include "otbn_model_agent.sv"

endpackage: otbn_model_agent_pkg
