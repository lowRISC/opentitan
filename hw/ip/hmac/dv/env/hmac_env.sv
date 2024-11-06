// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_env extends cip_base_env #(.CFG_T               (hmac_env_cfg),
                                      .COV_T               (hmac_env_cov),
                                      .VIRTUAL_SEQUENCER_T (hmac_virtual_sequencer),
                                      .SCOREBOARD_T        (hmac_scoreboard));
  `uvm_component_utils(hmac_env)

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
  extern function void end_of_elaboration_phase(uvm_phase phase);
endclass : hmac_env


function hmac_env::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new

function void hmac_env::build_phase(uvm_phase phase);
  super.build_phase(phase);

  // config hmac virtual interface
  if (!uvm_config_db#(hmac_vif)::get(this, "", "hmac_vif", cfg.hmac_vif)) begin
    `uvm_fatal(`gfn, "failed to get hmac_vif from uvm_config_db")
  end
endfunction : build_phase

function void hmac_env::end_of_elaboration_phase(uvm_phase phase);
  dv_base_mem mem;
  super.end_of_elaboration_phase(phase);
  // hmac mem supports partial write, set it after ral model is locked
  `downcast(mem, get_mem_by_addr(cfg.ral, cfg.ral.get_addr_from_offset(HMAC_MSG_FIFO_BASE)))
  mem.set_mem_partial_write_support(1);
endfunction : end_of_elaboration_phase
