// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class nvm_otp_key_agent_cov extends dv_base_agent_cov #(nvm_otp_key_agent_cfg);
  `uvm_component_utils(nvm_otp_key_agent_cov)

  // Sampled by the monitor on every completed handshake.
  covergroup handshake_cg with function sample(nvm_otp_key_item item);
    kind_cp: coverpoint item.kind;
    seed_valid_cp: coverpoint item.seed_valid;
    req_to_ack_cycles_cp: coverpoint item.req_to_ack_cycles {
      bins short_delay  = {[0:2]};
      bins medium_delay = {[3:5]};
      bins long_delay   = {[6:$]};
    }
    kind_x_seed_valid_cross: cross kind_cp, seed_valid_cp;
    kind_x_req_to_ack_cycles_cross: cross kind_cp, req_to_ack_cycles_cp;
  endgroup : handshake_cg

  extern function new(string name = "", uvm_component parent = null);
endclass : nvm_otp_key_agent_cov

function nvm_otp_key_agent_cov::new(string name = "", uvm_component parent = null);
  super.new(name, parent);
  handshake_cg = new();
endfunction : new
