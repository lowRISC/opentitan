// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cheriot_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(cheriot_env_cfg),
    .COV_T(cheriot_env_cov)
  );
  `uvm_component_utils(cheriot_virtual_sequencer)


  `uvm_component_new

endclass
