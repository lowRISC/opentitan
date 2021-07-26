// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// genbits test vseq
class csrng_cmds_vseq extends csrng_base_vseq;
  `uvm_object_utils(csrng_cmds_vseq)

  `uvm_object_new

  bit [entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH-1:0]   entropy_val;
  csrng_item                                        cs_item, cs_item_clone, cs_item_q[NUM_HW_APPS][$];
  uint                                              num_cmds;
  bit [csrng_pkg::GENBITS_BUS_WIDTH-1:0]            genbits;


  task body();
    // TODO: Create/start entropy_src device sequence still under development. Will remove/modify
    // as necessary. Also consider making task if it stays.
    // TODO: Enhance to run all cmds in the queues

    // Create entropy_src sequence
    m_entropy_src_pull_seq = push_pull_device_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)::type_id::
         create("m_entropy_src_pull_seq");
    // Create csrng_cmd host sequences and cs_item
    for (int i = 0; i < NUM_HW_APPS; i++) begin
      m_edn_push_seq[i] = push_pull_host_seq#(csrng_pkg::CSRNG_CMD_WIDTH)::type_id::create($sformatf("m_edn_push_seq[%0d]", i));
      cs_item           = csrng_item::type_id::create("cs_item");
    end

    // Generate queues of csrng commands
    for (int i = 0; i < NUM_HW_APPS; i++) begin
      // TODO: randomize num_cmds
      for (int j = 0; j < 1; j++) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(cs_item,
                                       cs_item.acmd  == csrng_pkg::INS;
                                       cs_item.flags == 4'h1;
                                       cs_item.glen  == 'h0;)
        `downcast(cs_item_clone, cs_item.clone());
        cs_item_q[i].push_back(cs_item_clone);
      end

      // Print cs_items
      foreach (cs_item_q[i][j])
        `uvm_info(`gfn, $sformatf("cs_item_q[%0d][%0d]: %s", i, j, cs_item_q[i][j].convert2string()), UVM_DEBUG)
    end

    // Start entropy_src
    fork
      begin
        // TODO: randomize entropy/fips
        cfg.m_entropy_src_agent_cfg.add_d_user_data(384'hdeadbeef);
        cfg.m_entropy_src_agent_cfg.add_d_user_data(384'hbeefdead);
        m_entropy_src_pull_seq.start(p_sequencer.entropy_src_sequencer_h);
      end
    join_none

    // Send commands to DUT
    for (int i = 0; i < NUM_HW_APPS; i++) begin
      foreach (cs_item_q[i][j])begin
        send_cmd_req(i, cs_item_q[i][j]);
      end
    end

    // Wait for DUT to ack commands
    for (int i = 0; i < NUM_HW_APPS; i++) begin
      cfg.m_edn_agent_cfg[i].vif.wait_cmd_ack();
    end

        // TODO: add other commands
        // //generate cmd
        // send_cmd_req(.acmd(csrng_pkg::GEN), .clen(4'h0), .flags(4'h0), .glen(19'h1));
        // genbits = ctr_drbg_generate();

        // //reseed cmd
        // send_cmd_req(.acmd(csrng_pkg::RES), .clen(4'h0), .flags(4'h0), .glen(19'h0));
        // ctr_drbg_reseed(384'hbeefdead);

        // //update cmd
        // cmd_data_q.push_back(32'hdeadbeef);
        // send_cmd_req(.acmd(csrng_pkg::UPD), .clen(4'h1), .flags(4'h0), .glen(19'h0), .data_q(cmd_data_q));
        // csrng_update(384'hdeadbeef);

        // send_cmd_req(.acmd(csrng_pkg::UNI), .clen(4'h0), .flags(4'h0), .glen(19'h0));

    if (cfg.chk_int_state) begin
      for (int i = 0; i < NUM_HW_APPS; i++)
        cfg.check_int_state(i);
    end

  endtask : body
endclass : csrng_cmds_vseq
