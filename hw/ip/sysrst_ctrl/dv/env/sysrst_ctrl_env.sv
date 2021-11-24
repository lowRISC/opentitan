// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sysrst_ctrl_env extends cip_base_env #(
    .CFG_T              (sysrst_ctrl_env_cfg),
    .COV_T              (sysrst_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(sysrst_ctrl_virtual_sequencer),
    .SCOREBOARD_T       (sysrst_ctrl_scoreboard)
  );
  `uvm_component_utils(sysrst_ctrl_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

endclass
