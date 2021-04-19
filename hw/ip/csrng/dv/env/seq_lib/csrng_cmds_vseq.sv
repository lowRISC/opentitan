// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// genbits test vseq
class csrng_cmds_vseq extends csrng_base_vseq;
  `uvm_object_utils(csrng_cmds_vseq)

  `uvm_object_new

  rand bit [entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH-1:0]   entropy_val;
  bit [csrng_pkg::CSRNG_CMD_WIDTH-1:0]                   cmd_data, cmd_data_q[$];
  bit [csrng_pkg::GENBITS_BUS_WIDTH-1:0]                 genbits;


  task body();
    // Enable CSRNG, Disable AES Cipher Core
    ral.ctrl.enable.set(1'b1);
    ral.ctrl.aes_cipher_disable.set(cfg.aes_cipher_disable);
    csr_update(.csr(ral.ctrl));

    // TODO: Create/start entropy_src device sequence still under development. Will remove/modify
    // as necessary. Also consider making task if it stays.
    // TODO: csrng_cmds_vseq still under development.

    // Create and start entropy_src device sequence
    m_entropy_src_pull_seq = push_pull_device_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)::type_id::
         create("m_entropy_src_pull_seq");
    // Create csrng_cmd host sequence
    m_edn_push_seq = push_pull_host_seq#(csrng_pkg::CSRNG_CMD_WIDTH)::type_id::create("m_edn_push_seq");

    fork
      begin
//      for (int i = 0; i < num_trans; i++) begin
//        `DV_CHECK_STD_RANDOMIZE_FATAL(entropy_val);
          // Set FIPS bit to 0
          // TODO: Not always 0, maybe leave randomized
//        entropy_val[entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH] = 1'b0;
//          entropy_val = ;
          cfg.m_entropy_src_agent_cfg.add_d_user_data(384'hdeadbeef);
          cfg.m_entropy_src_agent_cfg.add_d_user_data(384'hbeefdead);
//      end
        m_entropy_src_pull_seq.start(p_sequencer.entropy_src_sequencer_h);
      end

      begin
        //instantiate cmd
//        for (int i = 0; i < 1; i++)
//          cmd_data_q.push_back(32'hdeadbeef);
//        send_cmd_req(.acmd(csrng_pkg::INS), .clen(4'h1), .flags(4'h1), .glen(19'h0), .data_q(cmd_data_q));
        send_cmd_req(.acmd(csrng_pkg::INS), .clen(4'h0), .flags(4'h0), .glen(19'h0));
        ctr_drbg_instantiate(384'hdeadbeef);

        //generate cmd
        send_cmd_req(.acmd(csrng_pkg::GEN), .clen(4'h0), .flags(4'h0), .glen(19'h1));
        genbits = ctr_drbg_generate();

        //reseed cmd
        send_cmd_req(.acmd(csrng_pkg::RES), .clen(4'h0), .flags(4'h0), .glen(19'h0));
        ctr_drbg_reseed(384'hbeefdead);

        //update cmd
        cmd_data_q.push_back(32'hdeadbeef);
        send_cmd_req(.acmd(csrng_pkg::UPD), .clen(4'h1), .flags(4'h0), .glen(19'h0), .data_q(cmd_data_q));
        csrng_update(384'hdeadbeef);

        send_cmd_req(.acmd(csrng_pkg::UNI), .clen(4'h0), .flags(4'h0), .glen(19'h0));
      end
    join_none

  endtask : body
endclass : csrng_cmds_vseq
