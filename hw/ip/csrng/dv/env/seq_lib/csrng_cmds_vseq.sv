// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_cmds_vseq extends csrng_base_vseq;
  `uvm_object_utils(csrng_cmds_vseq)
  `uvm_object_new

  csrng_item   cs_item, cs_item_q[NUM_HW_APPS + 1][$];
  uint         num_cmds, cmds_gen, cmds_sent, aes_halt_clks;
  bit          uninstantiate[NUM_HW_APPS + 1];

  function void gen_seed(uint app);
    bit [entropy_src_pkg::FIPS_BUS_WIDTH - 1:0]    fips;
    bit [entropy_src_pkg::CSRNG_BUS_WIDTH - 1:0]   entropy;

    `DV_CHECK_STD_RANDOMIZE_FATAL(fips)
    `DV_CHECK_STD_RANDOMIZE_FATAL(entropy)
    cfg.m_entropy_src_agent_cfg.add_d_user_data({fips, entropy});
  endfunction

  function void create_cmds(uint app);
    bit   uni;

    cs_item = new();
    // Start with instantiate command
    `DV_CHECK_RANDOMIZE_WITH_FATAL(cs_item,
                                   cs_item.acmd == csrng_pkg::INS;)
    if (cs_item.flags != MuBi4True) begin
      gen_seed(app);
    end
    cs_item_q[app].push_back(cs_item);

    // Randomize num_cmds and generate other commands
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_cmds, num_cmds inside
        { [cfg.num_cmds_min:cfg.num_cmds_max] };)
    `uvm_info(`gfn, $sformatf("num_cmds[%0d] = %0d", app, num_cmds), UVM_DEBUG)

    // Generate other commands
    for (int i = 0; i < num_cmds; i++) begin
       cs_item = new();
      `DV_CHECK_RANDOMIZE_WITH_FATAL(cs_item,
                                     cs_item.acmd inside { csrng_pkg::GEN,
                                                           csrng_pkg::RES,
                                                           csrng_pkg::UPD };)
      if ((cs_item.acmd == csrng_pkg::RES) && (cs_item.flags != MuBi4True)) begin
        gen_seed(app);
      end
      cs_item_q[app].push_back(cs_item);
    end

    // Predetermine if uninstantiate so final internal state is non-zero some of the time.
    `DV_CHECK_STD_RANDOMIZE_FATAL(uni)
    uninstantiate[app] = uni;

    if (uninstantiate[app]) begin
      cs_item = new();
      `DV_CHECK_RANDOMIZE_WITH_FATAL(cs_item,
                                     cs_item.acmd  == csrng_pkg::UNI;
                                     cs_item.clen  == 'h0;)
      cs_item_q[app].push_back(cs_item);
    end

    cmds_gen += cs_item_q[app].size();
  endfunction

  function void create_cmds_all_apps();
    cmds_gen = 0;
    cmds_sent = 0;
    // Generate queues of csrng commands
    for (int i = 0; i < NUM_HW_APPS + 1; i++) begin
      create_cmds(i);
    end
  endfunction

  function void print_cmds_all_apps();
    for (int i = 0; i < NUM_HW_APPS + 1; i++) begin
      foreach (cs_item_q[i][j]) begin
        `uvm_info(`gfn, $sformatf("cs_item_q[%0d][%0d]: %s", i, j,
            cs_item_q[i][j].convert2string()), UVM_DEBUG)
      end
    end
  endfunction

  task body();
    super.body();

    // Create entropy_src sequence
    m_entropy_src_pull_seq = push_pull_device_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)::
        type_id::create("m_entropy_src_pull_seq");
    // Create aes_halt sequence
    m_aes_halt_pull_seq = push_pull_host_seq#(1)::type_id::create("m_aes_halt_pull_seq");
    // Create edn host sequences
    for (int i = 0; i < NUM_HW_APPS; i++) begin
      m_edn_push_seq[i] = push_pull_host_seq#(csrng_pkg::CSRNG_CMD_WIDTH)::type_id::create
                                              ($sformatf("m_edn_push_seq[%0d]", i));
    end

    create_cmds_all_apps();
    print_cmds_all_apps();

    // Start entropy_src agent
    fork
      m_entropy_src_pull_seq.start(p_sequencer.entropy_src_sequencer_h);
    join_none

    // Send commands
    fork
      for (int i = 0; i < NUM_HW_APPS + 1; i++) begin
        automatic int j = i;
        fork
          begin
            foreach (cs_item_q[j][k]) begin
              send_cmd_req(.app(j), .cs_item(cs_item_q[j][k]));
              cmds_sent += 1;
            end
          end
        join_none;
      end

      do begin
        `uvm_info(`gfn, $sformatf("aes_halt_clks = %0d, cmds_sent = %0d, cmds_gen = %0d",
                  aes_halt_clks, cmds_sent, cmds_gen), UVM_DEBUG)
        if (cfg.aes_halt) begin
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(aes_halt_clks, aes_halt_clks inside
              { [cfg.min_aes_halt_clks:cfg.max_aes_halt_clks] };)
          cfg.clk_rst_vif.wait_clks(aes_halt_clks);
          m_aes_halt_pull_seq.start(p_sequencer.aes_halt_sequencer_h);
        end
        else begin
          cfg.clk_rst_vif.wait_clks(500);
        end
      end
      while (cmds_sent < cmds_gen);
    join

    // Check internal state, then uninstantiate if not already
    if (cfg.check_int_state) begin
      for (int i = 0; i < NUM_HW_APPS + 1; i++) begin
        cfg.check_internal_state(.app(i), .compare(1));
        if (!uninstantiate[i]) begin
          cs_item = new();
          `DV_CHECK_RANDOMIZE_WITH_FATAL(cs_item,
                                         cs_item.acmd  == csrng_pkg::UNI;
                                         cs_item.clen  == 'h0;)
          send_cmd_req(.app(i), .cs_item(cs_item));
        end
      end
    end
  endtask : body
endclass : csrng_cmds_vseq
