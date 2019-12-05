// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Xbar environment virtual sequencer
// ---------------------------------------------
class xbar_virtual_sequencer extends dv_base_virtual_sequencer #(.CFG_T(xbar_env_cfg),
                                                                 .COV_T(xbar_env_cov));

  tl_sequencer host_seqr[];
  tl_sequencer device_seqr[];

  `uvm_component_utils(xbar_virtual_sequencer)
  `uvm_component_new
endclass
