// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dcd_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(dcd_env_cfg),
    .COV_T(dcd_env_cov)
  );
  `uvm_component_utils(dcd_virtual_sequencer)


  `uvm_component_new

endclass
