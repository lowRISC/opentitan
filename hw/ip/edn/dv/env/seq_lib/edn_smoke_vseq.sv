// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_smoke_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_smoke_vseq)

  `uvm_object_new

  push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)   m_endpoint_pull_seq;

  task body();
    super.body();

    // Enable edn
    csr_wr(.csr(ral.ctrl), .value(1'b1));

    m_endpoint_pull_seq = push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)::type_id::
        create("m_endpoint_pull_seq");
    m_endpoint_pull_seq.start(p_sequencer.endpoint_sequencer_h[edn_env_pkg::NUM_ENDPOINTS-1]);

    // TODO: Compare to genbits from csrng_device_seq (not hardcode "deadbeef")
    `DV_CHECK_EQ_FATAL(cfg.m_endpoint_agent_cfg[edn_env_pkg::NUM_ENDPOINTS-1].vif.d_data, {1'b0, 32'hdeadbeef})
  endtask

endclass
