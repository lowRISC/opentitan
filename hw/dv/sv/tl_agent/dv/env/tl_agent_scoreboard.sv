// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ------------------------------------------------------------------------
// tl_agent scoreboard class
// Extend from common multi-streams scoreboard
// Use the device address map to determine the queue ID
// ------------------------------------------------------------------------
class tl_agent_scoreboard extends scoreboard_pkg::scoreboard #(.ITEM_T(tl_seq_item),
                                                               .CFG_T (tl_agent_env_cfg),
                                                               .COV_T (tl_agent_env_cov));
  int chan_prefix_len = 7;

  `uvm_component_utils(tl_agent_scoreboard)
  `uvm_component_new

  // "host_req_chan", "device_req_chan" -> queue "req_chan"
  // "host_rsp_chan", "device_rsp_chan" -> queue "rsp_chan"
  virtual function string get_queue_name(tl_seq_item tr, string port_name);
    if (port_name inside {"host_req_chan", "device_req_chan"}) return "req_chan";
    else                                                       return "rsp_chan";
  endfunction

endclass
