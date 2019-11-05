// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class tl_agent_cov extends uvm_component;
  `uvm_component_utils(tl_agent_cov)

  // Covergroup: pending_req_on_rst_cg
  // define bins for having pending request while on reset
  covergroup pending_req_on_rst_cg with function sample(bit req_pending);
    cp_req_pending: coverpoint req_pending {
      bins values[] = {0, 1};
    }
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    pending_req_on_rst_cg = new();
  endfunction : new

endclass
