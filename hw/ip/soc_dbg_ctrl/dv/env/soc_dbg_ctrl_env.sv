// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class soc_dbg_ctrl_env extends cip_base_env #(
    .CFG_T              (soc_dbg_ctrl_env_cfg),
    .COV_T              (soc_dbg_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(soc_dbg_ctrl_virtual_sequencer),
    .SCOREBOARD_T       (soc_dbg_ctrl_scoreboard)
  );
  `uvm_component_utils(soc_dbg_ctrl_env)

  tl_agent tl_jtag_agt;

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
endclass : soc_dbg_ctrl_env


function soc_dbg_ctrl_env::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new

function void soc_dbg_ctrl_env::build_phase(uvm_phase phase);
  super.build_phase(phase);
endfunction : build_phase

function void soc_dbg_ctrl_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
endfunction : connect_phase
