// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_agent_cfg extends dv_base_agent_cfg;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual csrng_if vif;

  push_pull_agent_cfg#(csrng_pkg::CSRNG_CMD_WIDTH)          m_cmd_push_agent_cfg;
  push_pull_agent_cfg#(csrng_pkg::FIPS_GENBITS_BUS_WIDTH)   m_genbits_push_agent_cfg;

  `uvm_object_utils_begin(csrng_agent_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  uint   min_cmd_ack_dly, max_cmd_ack_dly,
         min_genbits_dly, max_genbits_dly,
         min_genbits_rdy_dly, max_genbits_rdy_dly,
         min_cmd_rdy_dly, max_cmd_rdy_dly,
         reseed_cnt, generate_cnt, generate_between_reseeds_cnt;
  bit    cmd_zero_delays;
  bit    under_reset;

endclass
