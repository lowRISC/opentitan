// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_genbits_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_genbits_vseq)

  `uvm_object_new

  push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)   m_endpoint_pull_seq;

  bit [csrng_pkg::GENBITS_BUS_WIDTH - 1:0]      genbits;
  bit [entropy_src_pkg::FIPS_BUS_WIDTH - 1:0]   fips;
  bit [edn_pkg::ENDPOINT_BUS_WIDTH - 1:0]       edn_bus[edn_env_pkg::NUM_ENDPOINTS];

  task body();
    // TODO: Add prediction, compare in scoreboard
    // TODO: Multiple endpoints randomly requesting
    m_endpoint_pull_seq = push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)::type_id::
        create("m_endpoint_pull_seq");
    `DV_CHECK_STD_RANDOMIZE_FATAL(fips)
    `DV_CHECK_STD_RANDOMIZE_FATAL(genbits)
    cfg.m_csrng_agent_cfg.m_genbits_push_agent_cfg.add_h_user_data({fips, genbits});

    m_endpoint_pull_seq.start(p_sequencer.endpoint_sequencer_h[edn_env_pkg::NUM_ENDPOINTS-1]);

    edn_bus[edn_env_pkg::NUM_ENDPOINTS-1] = genbits[edn_pkg::ENDPOINT_BUS_WIDTH - 1:0];
    `DV_CHECK_EQ_FATAL(cfg.m_endpoint_agent_cfg[edn_env_pkg::NUM_ENDPOINTS-1].vif.d_data,
        {1'b0, fips, edn_bus[edn_env_pkg::NUM_ENDPOINTS-1]})
  endtask

endclass
