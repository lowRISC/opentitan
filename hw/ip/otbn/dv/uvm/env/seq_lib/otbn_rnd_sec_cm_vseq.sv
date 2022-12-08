// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test sequence to check both RND.RNG.DIGEST and RND.BUS.CONSISTENCY security countermeasures.
// The main skeleton is otbn_multi test in which we run multiple programs. It is better suited
// to see RND behaviour between different OTBN operations.
// Behaviour of the test changes with accordance to the randomized number of repeated EDN words
// as an answer to the RND request. If number of repeated EDN words is zero, only error will be
// about FIPS non-compliant cases. In the case of repeats being greater or equal than eight
// -the number of total EDN words for RND, only repetition errors will be seen.

class otbn_rnd_sec_cm_vseq extends otbn_multi_vseq;
  `uvm_object_utils(otbn_rnd_sec_cm_vseq)
  `uvm_object_new

  task body();
    // Do not do the end addr check because we are finishing the program abrubtly with an error.
    do_end_addr_check = 0;
    super.body();
  endtask

  // Overwrite it from base since now we also want to send same EDN data back to back
  virtual task _run_rnd_edn_rsp();
    forever begin
      bit [cip_base_pkg::EDN_BUS_WIDTH-1:0] entropy;
      int num_repeated_edn;
      @(negedge cfg.clk_rst_vif.clk);
      if(cfg.poll_rnd_edn_req() && ~cfg.rnd_vif.edn_rnd_ack_i) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(entropy)
        // Distrubution of num_repeated_edn will determine the behaviour of the test.
        // For detailed explanation see the comments above.
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_repeated_edn,
                                           num_repeated_edn dist { 0      :/ 25,
                                                                   [1:7]  :/ 25,
                                                                   8      :/ 25,
                                                                   9      :/ 25};)
        // If we have already loaded the agent with custom data, that means the previous
        // num_repeated_edn was nine and we overfilled our agent by one to test if EDN word
        // repetition would occur across 256b boundary.
        if (cfg.m_edn_pull_agent_cfgs[RndEdnIdx].has_d_user_data())
        // In this case, we want to fill the remaining 7 EDN words with "FIPS qualified"
        // randomness each time. Because creating a FIPS error is not important in this
        // case.
          repeat (otbn_pkg::EdnDataWidth/cip_base_pkg::EDN_BUS_WIDTH - 1)
            cfg.m_edn_pull_agent_cfgs[RndEdnIdx].add_d_user_data({1'b1, $urandom});
        else
          repeat (num_repeated_edn)
          // Note that if there are still some EDN packages remaining to be sent
          // (num_repeated_edn < 8) after filling up the edn_pull_agent with custom data,
          // responses from EDN will get randomized. That means FIPS field has half a
          // chance of being low reach time we send a new word for RND.
            cfg.m_edn_pull_agent_cfgs[RndEdnIdx].add_d_user_data({1'b1, entropy});
        // Wait until all EDN packages are collected for the next request polling.
        wait(cfg.rnd_vif.edn_rnd_ack_i);
      end
    end
  endtask

endclass : otbn_rnd_sec_cm_vseq
