// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// coverage for sampling all the combination of valid and ready
covergroup valid_ready_cg(string name, string path) with function sample(bit valid, bit ready);
  option.per_instance = 1;
  option.name         = {path, "::", name};

  cp_valid_ready: coverpoint {valid, ready};
endgroup : valid_ready_cg

// coverage for sampling all the combination of valid and ready
covergroup req_ack_cg(string name, string path) with function sample(bit req, bit ack);
  option.per_instance = 1;
  option.name         = {path, "::", name};

  // Not a possible combination if this is non-4-phases mode.
  // But this will happen in the 4 phases req-ack handshake.
  // In that case, this value has to happen after 2'b11, so no need to sample it
  cp_req_ack: coverpoint {req, ack} {
    ignore_bins ack_wo_req = {2'b01};
  }
endgroup : req_ack_cg

class push_pull_agent_cov #(parameter int HostDataWidth = 32,
                            parameter int DeviceDataWidth = HostDataWidth)
  extends dv_base_agent_cov #(
    push_pull_agent_cfg#(HostDataWidth, DeviceDataWidth)
);

  `uvm_component_param_utils(push_pull_agent_cov#(HostDataWidth, DeviceDataWidth))
  `uvm_component_new

  valid_ready_cg m_valid_ready_cg;
  req_ack_cg m_req_ack_cg;
  function void build_phase(uvm_phase phase);
    if (cfg.agent_type == PushAgent) begin
      m_valid_ready_cg = new("m_valid_ready_cg", `gfn);
    end else begin
      m_req_ack_cg = new("m_req_ack_cg", `gfn);
    end
  endfunction : build_phase

endclass
