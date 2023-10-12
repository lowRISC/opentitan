// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_smoke_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_smoke_vseq)

  `uvm_object_new

  push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)   m_endpoint_pull_seq[MAX_NUM_ENDPOINTS];

  task body();
    super.body();

    // Create single endpoint sequence
    m_endpoint_pull_seq[0] = push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)::type_id::
        create("m_endpoint_pull_seq[0]");

    // Send instantiate cmd
    wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(csrng_pkg::INS), .clen(0), .flags(MuBi4False),
           .glen(0), .mode(edn_env_pkg::SwMode));

    // Request data
    m_endpoint_pull_seq[0] = push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)::type_id::
        create("m_endpoint_pull_seq[0]");
    m_endpoint_pull_seq[0].num_trans = csrng_pkg::GENBITS_BUS_WIDTH/ENDPOINT_BUS_WIDTH;
    fork
      m_endpoint_pull_seq[0].start(p_sequencer.endpoint_sequencer_h[0]);
    join_none

    // Send generate cmd
    wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(csrng_pkg::GEN), .clen(0), .flags(MuBi4False),
           .glen(1), .mode(edn_env_pkg::SwMode));

    // Send uninstantiate cmd
    `DV_CHECK_STD_RANDOMIZE_FATAL(flags)
    wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(csrng_pkg::UNI), .clen(0), .flags(flags),
           .glen(0), .mode(edn_env_pkg::SwMode));
  endtask

endclass
