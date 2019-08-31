// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_timer_env extends cip_base_env #(
        .CFG_T               (rv_timer_env_cfg),
        .COV_T               (rv_timer_env_cov),
        .VIRTUAL_SEQUENCER_T (rv_timer_virtual_sequencer),
        .SCOREBOARD_T        (rv_timer_scoreboard)
    );
  `uvm_component_utils(rv_timer_env)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

endclass
