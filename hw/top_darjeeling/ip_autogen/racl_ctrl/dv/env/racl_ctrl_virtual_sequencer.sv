// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_ctrl_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(racl_ctrl_env_cfg),
    .COV_T(racl_ctrl_env_cov)
  );
  `uvm_component_utils(racl_ctrl_virtual_sequencer)


  `uvm_component_new

endclass
