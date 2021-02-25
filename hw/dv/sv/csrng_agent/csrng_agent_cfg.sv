// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_agent_cfg extends dv_base_agent_cfg;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual csrng_if vif;

  push_pull_agent_cfg#(csrng_pkg::CSRNG_CMD_WIDTH)          m_req_push_agent_cfg;
  push_pull_agent_cfg#(csrng_pkg::FIPS_GENBITS_BUS_WIDTH)   m_genbits_push_agent_cfg;

  `uvm_object_utils_begin(csrng_agent_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  // TODO: set in testcase
  uint   min_cmd_ack_dly=2, max_cmd_ack_dly=2;
  uint   min_genbits_dly=10, max_genbits_dly=10;

endclass
