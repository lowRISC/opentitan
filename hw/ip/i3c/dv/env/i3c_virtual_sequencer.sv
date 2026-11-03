// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i3c_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(i3c_env_cfg),
    .COV_T(i3c_env_cov)
  );
  `uvm_component_utils(i3c_virtual_sequencer)

  `uvm_component_new

endclass
