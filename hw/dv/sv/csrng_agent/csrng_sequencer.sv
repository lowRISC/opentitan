// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_sequencer extends dv_base_sequencer #(
    .ITEM_T (csrng_item),
    .CFG_T  (csrng_agent_cfg)
);
  `uvm_component_param_utils(csrng_sequencer)

  push_pull_sequencer#(.HostDataWidth(csrng_pkg::CSRNG_CMD_WIDTH))          m_req_push_sequencer;
  push_pull_sequencer#(.HostDataWidth(csrng_pkg::FIPS_GENBITS_BUS_WIDTH))   m_genbits_push_sequencer;

  `uvm_component_new

endclass
