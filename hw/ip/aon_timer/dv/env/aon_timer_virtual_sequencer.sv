// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aon_timer_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(aon_timer_env_cfg),
    .COV_T(aon_timer_env_cov)
  );
  `uvm_component_utils(aon_timer_virtual_sequencer)


  `uvm_component_new

endclass
