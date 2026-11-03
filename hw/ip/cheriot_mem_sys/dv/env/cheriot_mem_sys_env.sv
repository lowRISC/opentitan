// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cheriot_mem_sys_env extends cip_base_env #(
    .CFG_T              (cheriot_mem_sys_env_cfg),
    .COV_T              (cheriot_mem_sys_env_cov),
    .VIRTUAL_SEQUENCER_T(cheriot_mem_sys_virtual_sequencer),
    .SCOREBOARD_T       (cheriot_mem_sys_scoreboard)
  );
  `uvm_component_utils(cheriot_mem_sys_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

endclass
