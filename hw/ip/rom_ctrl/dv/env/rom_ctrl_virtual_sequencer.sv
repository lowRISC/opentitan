// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(rom_ctrl_env_cfg),
    .COV_T(rom_ctrl_env_cov)
  );
  `uvm_component_utils(rom_ctrl_virtual_sequencer)

  kmac_app_sequencer kmac_sequencer_h;

  `uvm_component_new

endclass
