// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_cmds_vseq extends csrng_base_vseq;
  `uvm_object_utils(csrng_cmds_vseq)

  `uvm_object_new

  bit [entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH-1:0]   entropy_val;
  csrng_item                                        cs_item, cs_item_clone, cs_item_q[NUM_HW_APPS][$];
  uint                                              cmds_gen, cmds_sent;
  bit [csrng_pkg::GENBITS_BUS_WIDTH-1:0]            genbits;
  bit                                               uninstantiate;

  task body();
    // TODO: Add/randomize other commands. Use/add prediction for entropy from entropy_src agent.

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
      `DV_CHECK_RANDOMIZE_WITH_FATAL(cs_item,
                                     cs_item.acmd  == csrng_pkg::INS;
                                     cs_item.flags == 4'h1;
                                     cs_item.clen  inside {[0:12]};)
      `downcast(cs_item_clone, cs_item.clone());
      cs_item_q[i].push_back(cs_item_clone);

      `DV_CHECK_RANDOMIZE_WITH_FATAL(cs_item,
                                     cs_item.acmd  == csrng_pkg::GEN;
                                     cs_item.flags == 4'h0;
                                     cs_item.clen  == 4'h0;
                                     cs_item.glen inside {[1:32]};)
      `downcast(cs_item_clone, cs_item.clone());
      cs_item_q[i].push_back(cs_item_clone);

      // Randomize whether to add an uninstantiate command
      // so it checks internal state without uninstantiate sometimes
      `DV_CHECK_STD_RANDOMIZE_FATAL(uninstantiate)
      if (uninstantiate) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(cs_item,
                                       cs_item.acmd  == csrng_pkg::UNI;)
        `downcast(cs_item_clone, cs_item.clone());
        cs_item_q[i].push_back(cs_item_clone);
      end
    end

    // Print cs_items
    for (int i = 0; i < NUM_HW_APPS; i++) begin
      foreach (cs_item_q[i][j]) begin
        cmds_gen += 1;
        `uvm_info(`gfn, $sformatf("cs_item_q[%0d][%0d]: %s", i, j, cs_item_q[i][j].convert2string()), UVM_DEBUG)
      end
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

    // Send commands, wait for acks
    fork
      for (int i = 0; i < NUM_HW_APPS; i++) begin
        automatic int j = i;
        fork
          begin
            foreach (cs_item_q[j][k]) begin
              send_cmd_req(j, cs_item_q[j][k]);
              cmds_sent += 1;
            end
          end
        join_none;
      end

      wait (cmds_sent == cmds_gen);
    join

    // Check internal state
    if (cfg.chk_int_state) begin
      for (int i = 0; i < NUM_HW_APPS; i++)
        cfg.check_int_state(i);
    end

  endtask : body
endclass : csrng_cmds_vseq
