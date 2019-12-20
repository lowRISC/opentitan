// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Covergroup: pending_req_on_rst_cg
// define bins for having pending request while on reset
covergroup pending_req_on_rst_cg(string name) with function sample(bit req_pending);
  option.per_instance = 1;
  option.name         = name;
  cp_req_pending: coverpoint req_pending {
    bins values[] = {0, 1};
  }
endgroup

// coverage for sampling all the values of outstanding req, up to its max
covergroup max_outstanding_cg(string name, int max_outstanding) with function
    sample(int num_outstanding);
  option.per_instance = 1;
  option.name         = name;
  cp_num_of_outstanding: coverpoint num_outstanding {
    bins values[]  = {[1:max_outstanding]};
  }
endgroup : max_outstanding_cg

class tl_agent_cov extends dv_base_agent_cov #(tl_agent_cfg);
  pending_req_on_rst_cg pending_req_on_rst_cg;
  max_outstanding_cg    max_outstanding_cg;

  `uvm_component_utils(tl_agent_cov)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    pending_req_on_rst_cg = new(`gfn);
    max_outstanding_cg    = new(`gfn, cfg.max_outstanding_req);
  endfunction : build_phase
endclass
