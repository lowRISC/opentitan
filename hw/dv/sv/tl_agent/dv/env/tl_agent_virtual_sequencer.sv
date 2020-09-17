// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// tl_agent environment virtual sequencer
// ---------------------------------------------
class tl_agent_virtual_sequencer extends dv_base_virtual_sequencer #(.CFG_T(tl_agent_env_cfg),
                                                                     .COV_T(tl_agent_env_cov));

  tl_sequencer host_seqr;
  tl_sequencer device_seqr;

  `uvm_component_utils(tl_agent_virtual_sequencer)
  `uvm_component_new
endclass
