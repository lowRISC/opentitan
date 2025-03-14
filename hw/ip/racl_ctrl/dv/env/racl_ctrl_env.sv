// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_ctrl_env extends cip_base_env #(
    .CFG_T              (racl_ctrl_env_cfg),
    .COV_T              (racl_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(racl_ctrl_virtual_sequencer),
    .SCOREBOARD_T       (racl_ctrl_scoreboard)
  );
  `uvm_component_utils(racl_ctrl_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

endclass
