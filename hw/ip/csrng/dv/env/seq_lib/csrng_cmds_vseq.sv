// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// genbits test vseq
class csrng_cmds_vseq extends csrng_base_vseq;
  `uvm_object_utils(csrng_cmds_vseq)

  `uvm_object_new

  rand bit [entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH-1:0]   entropy_val;

  push_pull_device_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)   m_entropy_src_pull_seq;
  push_pull_host_seq#(csrng_pkg::CSRNG_CMD_WIDTH)                m_edn_push_seq;

  task body();
    // Enable CSRNG, Disable AES Cipher Core
    ral.ctrl.enable.set(1'b1);
    ral.ctrl.aes_cipher_disable.set(cfg.aes_cipher_disable);
    csr_update(.csr(ral.ctrl));

    // TODO: Create/start entropy_src device sequence still under development. Will remove/modify
    // as necessary. Also consider making task if it stays.
    // Create and start entropy_src device sequence
    m_entropy_src_pull_seq = push_pull_device_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)::type_id::
         create("m_entropy_src_pull_seq");

    for (int i = 0; i < num_trans; i++) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(entropy_val);
      // Set FIPS bit to 0
      // TODO: Not always 0, maybe leave randomized
      entropy_val[entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH] = 1'b0;
      cfg.m_entropy_src_agent_cfg.add_d_user_data(entropy_val);
    end
//    m_entropy_src_pull_seq.start(p_sequencer.entropy_src_sequencer_h);

    // Create and start csrng host sequence
    m_edn_push_seq = push_pull_host_seq#(csrng_pkg::CSRNG_CMD_WIDTH)::type_id::create("m_edn_push_seq");

    acmd  = csrng_pkg::INS;
    clen  = 4'h0;
    flags = 4'h1;
    csrng_cmd = {glen, flags, clen, acmd};

    // TODO: Consider making task
    cfg.m_edn_agent_cfg.m_cmd_push_agent_cfg.add_h_user_data(csrng_cmd);
    m_edn_push_seq.num_trans = 1;
    m_edn_push_seq.start(p_sequencer.edn_sequencer_h.m_cmd_push_sequencer);

    // Wait for cmd_ack
    cfg.m_edn_agent_cfg.vif.wait_cmd_ack();

  endtask : body

endclass : csrng_cmds_vseq
