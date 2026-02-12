// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test entropy_src interrupts

class entropy_src_intr_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_intr_vseq)

  `uvm_object_new

  push_pull_host_seq#(`RNG_BUS_WIDTH)          m_rng_push_seq;
  push_pull_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)   m_csrng_pull_seq;

  bit [15:0]  fips_thresh, bypass_thresh;
  bit [15:0]  fips_hi_thresh, fips_lo_thresh;
  bit [15:0]  bypass_hi_thresh, bypass_lo_thresh;
  bit [15:0]  one_eighth;

  task test_es_entropy_valid();
    // Turn off the dut while we write to its registers.
    disable_dut();
    // Route the entropy to the SW output.
    csr_wr(.ptr(ral.entropy_control.es_route), .value(prim_mubi_pkg::MuBi4True));
    // Turn off ov mode since we don't need to observe the post helth test entropy
    // and don't want to insert entropy via the register FW_OV_WR_DATA.
    csr_wr(.ptr(ral.fw_ov_control), .value(32'h99));
    // Allow for entropy to be read via the SW register.
    csr_wr(.ptr(ral.conf.entropy_data_reg_enable), .value(prim_mubi_pkg::MuBi4True));
    // Enable only entropy valid interrupts.
    csr_wr(.ptr(ral.intr_enable), .value(1 << EntropyValid));
    // Turn on the DUT.
    enable_dut();

    // Create and start rng host sequence.
    m_rng_push_seq = push_pull_host_seq#(`RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");
    m_rng_push_seq.num_trans = entropy_src_pkg::CSRNG_BUS_WIDTH/`RNG_BUS_WIDTH;
    run_rng_host_seq(m_rng_push_seq);

    // Wait for the entropy_valid interrupt.
    csr_spinwait(.ptr(ral.intr_state.es_entropy_valid), .exp_data(1'b1));
    // Expect and clear interrupt bit for entropy valid interrupts.
    check_interrupts(.interrupts((1 << EntropyValid)), .check_set(1'b1));
  endtask // test_es_entropy_valid

  task test_es_observe_fifo_ready();
    // Turn off the dut while we write to its registers.
    disable_dut();
    // Turn on firmware override mode to be able to read from the observe FIFO.
    csr_wr(.ptr(ral.fw_ov_control.fw_ov_mode), .value(prim_mubi_pkg::MuBi4True));
    // Set the observe fifo depth threshold to a low number to trigger the interrupt faster.
    csr_wr(.ptr(ral.observe_fifo_thresh.observe_fifo_thresh), .value(7'b0000100));
    // Enable only es_observe_fifo_ready interrupts.
    csr_wr(.ptr(ral.intr_enable), .value(1 << ObserveFifoReady));
    // Turn on the DUT.
    enable_dut();

    // Create and start rng host sequence.
    m_rng_push_seq = push_pull_host_seq#(`RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");
    m_rng_push_seq.num_trans = entropy_src_pkg::CSRNG_BUS_WIDTH/`RNG_BUS_WIDTH;
    run_rng_host_seq(m_rng_push_seq);

    // Wait for the observe_fifo_ready interrupt.
    csr_spinwait(.ptr(ral.intr_state.es_observe_fifo_ready), .exp_data(1'b1));
    // Expect and clear interrupt bit for observe FIFO ready interrupts.
    check_interrupts(.interrupts((1 << ObserveFifoReady)), .check_set(1'b1));
  endtask // test_es_observe_fifo_ready

  // This function checks whether the arrangement of the 16 possible RNG values
  // fail the Markov test.
  function bit check_for_markov_failure(bit [3:0] rng_arr[16]);
    int transition_cnts[4] = '{default: 0};
    int max_cnt[$], min_cnt[$];
    // Loop over the 8 pairs of bits.
    for (int i = 0; i < 8; i++) begin
      // Loop over the 4 bit lanes.
      for (int j = 0; j < 4; j++) begin
        // XORing tells us whether there is a transition or not.
        transition_cnts[j] += rng_arr[2*i][j] ^ rng_arr[2*i+1][j];
      end
    end
    // Get the min and max number of transitions out of the 4 lanes.
    min_cnt = transition_cnts.min();
    max_cnt = transition_cnts.max();
    // Return true if the sequence would fail the Markov test with the lo/hi thresholds
    // set to 1/16th below/above the average of 1/2. On average 1/2 of the pairs should
    // have a transition (e.g. 01 or 10).
    return (max_cnt.pop_back() > 5) || (min_cnt.pop_back() < 3);
  endfunction

  task test_es_health_test_failed();
    int BucketHtDataWidth = entropy_src_pkg::bucket_ht_data_width(`RNG_BUS_WIDTH);
    int NumBuckets = 2**BucketHtDataWidth;
    int unsigned NumBucketHtInst = entropy_src_pkg::num_bucket_ht_inst(`RNG_BUS_WIDTH);
    int num_valid_rng_trans = 0;
    int num_invalid_rng_trans = 0;
    int bundles_found = 0;
    // The actual RNG symbols are generated based on this array. For configurations with a symbol
    // size greater than 4 bits, every 4 consecutive lanes of the symbols are chosen from multiple,
    // shuffled versions of this array.
    bit [3:0] rng4bits_arr[16] = '{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15};
    bit [`RNG_BUS_WIDTH-1:0] rng_bits_arr[16];
    rng_val_t rng_arr[16];
    rng_val_t rng_val;
    string rng_str;
    state_e alert_state = entropy_src_main_sm_pkg::AlertHang;

    // Create the RNG and CSRNG host sequences.
    m_rng_push_seq = push_pull_host_seq#(`RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");
    m_csrng_pull_seq = push_pull_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)::
         type_id::create("m_csrng_pull_seq");

    // Turn off the dut while we write to its registers.
    disable_dut();
    // Turn off firmware override insert mode.
    csr_wr(.ptr(ral.fw_ov_control.fw_ov_entropy_insert), .value(prim_mubi_pkg::MuBi4False));
    // Enable only es_health_test_failed interrupts.
    csr_wr(.ptr(ral.intr_enable), .value(1 << HealthTestFailed));
    csr_wr(.ptr(ral.alert_threshold), .value(32'hfffe0001));
    // Make the entropy readable via FW or HW depending on the value of cfg.es_route_sw.
    csr_wr(.ptr(ral.entropy_control.es_route), .value(cfg.es_route_sw));
    csr_wr(.ptr(ral.conf.entropy_data_reg_enable), .value(cfg.es_route_sw));
    // Bypass the conditioner in boot mode.
    if (cfg.which_ht_state inside {BootHTRunning, BootPhaseDone}) begin
      csr_wr(.ptr(ral.entropy_control.es_type), .value(prim_mubi_pkg::MuBi4True));
      csr_wr(.ptr(ral.conf.fips_enable), .value(prim_mubi_pkg::MuBi4False));
    end
    // Do not bypass the conditioner in continuous mode.
    if (cfg.which_ht_state inside {StartupFail1, ContHTRunning}) begin
      csr_wr(.ptr(ral.entropy_control.es_type), .value(prim_mubi_pkg::MuBi4False));
      csr_wr(.ptr(ral.conf.fips_enable), .value(prim_mubi_pkg::MuBi4True));
    end

    case (cfg.which_ht_state)
      BootHTRunning : begin
        // BootHTRunning is entered directly after enablement.
        // Therefore, only one CSRNG transaction is needed to check
        // that the ES stops producing entropy.
        m_csrng_pull_seq.num_trans = 1;
        // Set num_invalid_rng_trans to add invalid h_user_data to the RNG agent.
        num_invalid_rng_trans = cfg.dut_cfg.bypass_window_size/`RNG_BUS_WIDTH;
        // For 1 CSRNG transaction we need 384/`RNG_BUS_WIDTH RNG transactions.
        m_rng_push_seq.num_trans = cfg.dut_cfg.bypass_window_size/`RNG_BUS_WIDTH;
      end
      BootPhaseDone : begin
        // To enter BootPhaseDone, we need a valid transaction before failing the HT.
        // Therefore, two CSRNG transactions are needed. The first one gets the ES main SM into
        // BootPhaseDone and the second one is needed to check that the ES stops producing entropy.
        m_csrng_pull_seq.num_trans = 2;
        // Set num_valid_rng_trans to add valid h_user_data to the RNG agent.
        num_valid_rng_trans = cfg.dut_cfg.bypass_window_size/`RNG_BUS_WIDTH;
        // Set num_invalid_rng_trans to add invalid h_user_data to the RNG agent.
        num_invalid_rng_trans = cfg.dut_cfg.bypass_window_size/`RNG_BUS_WIDTH;
        // For 2 CSRNG transactions we need 2*384/`RNG_BUS_WIDTH RNG transactions.
        m_rng_push_seq.num_trans = 2*cfg.dut_cfg.bypass_window_size/`RNG_BUS_WIDTH;
      end
      StartupFail1  : begin
        // To enter StartupFail1, we need a failing transaction before failing the HT again.
        // Therefore, only one CSRNG transaction is needed to check that the
        // ES stops producing entropy.
        m_csrng_pull_seq.num_trans = 1;
        // Set num_invalid_rng_trans to add invalid h_user_data to the RNG agent.
        num_invalid_rng_trans = 2*cfg.dut_cfg.fips_window_size;
        // For 2 CSRNG transactions we need 2*2048/`RNG_BUS_WIDTH RNG transactions.
        m_rng_push_seq.num_trans = 2*cfg.dut_cfg.fips_window_size;
      end
      ContHTRunning : begin
        // To enter ContHTRunning, we need one valid transaction before failing the HT.
        // Therefore, two CSRNG transactions are needed.
        m_csrng_pull_seq.num_trans = 2;
        // Set num_valid_rng_trans to add valid h_user_data to the RNG agent. We need twice the
        // amount of entropy to provide for 1 CSRNG transaction in the continuous mode.
        num_valid_rng_trans = 2*cfg.dut_cfg.fips_window_size;
        // Set num_invalid_rng_trans to add invalid h_user_data to the RNG agent.
        num_invalid_rng_trans = cfg.dut_cfg.fips_window_size;
        // For the 2 CSRNG transactions we need 3*2048 RNG transactions.
        m_rng_push_seq.num_trans = 3*cfg.dut_cfg.fips_window_size;
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid fail state! (bug in environment)")
      end
    endcase
    // Shuffle the RNG array to randomize the RNG inputs. If we are testing the Markov failure,
    // our valid sequence needs to pass the Markov test. For all the other tests, having an even
    // distribution of RNG inputs 0-15 suffices to pass. Every 4 consecutive lanes of the symbols
    // are chosen from multiple, shuffled versions of this array.
    for (int i = 0; i < `RNG_BUS_WIDTH/4; i++) begin
      do begin
        rng4bits_arr.shuffle();
      end while (check_for_markov_failure(rng4bits_arr) && (cfg.which_ht_fail == markov_ht_fail));
      rng_str = "";
      for (int j = 0; j < 16; j++) begin
        rng_bits_arr[j][i*4 +: 4] = rng4bits_arr[j];
        rng_str = $sformatf("%s%0x ", rng_str, rng4bits_arr[j]);
      end
      `uvm_info(`gfn,
          $sformatf("rng_arr lanes %2d - %2d: %s", i*4, i*4 + 3, rng_str),
          UVM_MEDIUM)
    end
    rng_arr = rng_bits_arr;

    // Add h_user_data to the RNG agent for each valid transaction.
    for (int i = 0; i < num_valid_rng_trans; i++) begin
      rng_val = rng_arr[i%16];
      cfg.m_rng_agent_cfg.add_h_user_data(rng_val);
    end

    case (cfg.which_ht_fail)
      repcnt_ht_fail: begin // Repetition count test
        `uvm_info(`gfn, $sformatf("repcnt_ht_fail"), UVM_MEDIUM)
        // Set a low threshold to introduce ht fails.
        // For our valid inputs a threshold of 10 suffices, since each subsequence of
        // 16 inputs contains all of the numbers 0-15 and since exactly half bits are
        // ones on each lane, the maximum number of repetitions is 8.
        fips_thresh = 16'h000a;
        bypass_thresh = 16'h000a;
        csr_wr(.ptr(ral.repcnt_thresholds), .value({bypass_thresh, fips_thresh}));
        enable_dut();
        repcnt_ht_fail_seq(m_rng_push_seq, num_invalid_rng_trans);
      end
      adaptp_ht_fail: begin // Adaptive proportion test
        `uvm_info(`gfn, $sformatf("adaptp_ht_fail"), UVM_MEDIUM)
        // The number of ones is window size in bits per transaction / 2 bit states. Set the
        // thresholds below such that the valid RNG subsequence passes. Using the same reasoning as
        // for repcnt_ht_fail, we know that exactly half of the bits are ones. The bypass
        // thresholds need to be a bit more loose due to the small window size.
        fips_thresh = cfg.dut_cfg.fips_window_size / 2;
        bypass_thresh = cfg.dut_cfg.bypass_window_size / `RNG_BUS_WIDTH / 2;
        fips_hi_thresh = fips_thresh + 1;
        fips_lo_thresh = fips_thresh - 1;
        bypass_hi_thresh = bypass_thresh + 3;
        bypass_lo_thresh = bypass_thresh - 3;
        adaptp_ht_fail_seq(m_rng_push_seq, fips_lo_thresh, fips_hi_thresh,
                           bypass_lo_thresh, bypass_hi_thresh, num_invalid_rng_trans);
      end
      bucket_ht_fail: begin // Bucket test
        `uvm_info(`gfn, $sformatf("bucket_ht_fail"), UVM_MEDIUM)
        // We know that the numbers 0-15 are evenly distributed. So we get our bucket threshold
        // by calculating window size in bits / bucket size * number of buckets * number of
        // bucket groups).
        fips_thresh = cfg.dut_cfg.fips_window_size * `RNG_BUS_WIDTH /
            (BucketHtDataWidth * NumBuckets * NumBucketHtInst) + 1;
        bypass_thresh = cfg.dut_cfg.bypass_window_size /
            (BucketHtDataWidth * NumBuckets * NumBucketHtInst) + 1;
        bucket_ht_fail_seq(m_rng_push_seq, fips_thresh, bypass_thresh, num_invalid_rng_trans);
      end
      markov_ht_fail: begin // Markov test
        `uvm_info(`gfn, $sformatf("markov_ht_fail"), UVM_MEDIUM)
        // We know our sequence passes check_for_markov_failure(). We get our thresholds by
        // calculating window size in bits / RNG_BUS_WIDTH / 2 bit states / 2 bits per sample
        // and then adding/subtracting 1/8th for the hi/low thresholds.
        fips_thresh = cfg.dut_cfg.fips_window_size / 4;
        bypass_thresh = cfg.dut_cfg.bypass_window_size / `RNG_BUS_WIDTH / 4;
        one_eighth = ((fips_thresh - 1) / 8 != 0) ? (fips_thresh - 1) / 8 : 1;
        fips_hi_thresh = fips_thresh + one_eighth + 1;
        fips_lo_thresh = fips_thresh - one_eighth - 1;
        one_eighth = ((bypass_thresh - 1) / 8 != 0) ? (bypass_thresh - 1) / 8 : 1;
        bypass_hi_thresh = bypass_thresh + one_eighth + 1;
        bypass_lo_thresh = bypass_thresh - one_eighth - 1;
        markov_ht_fail_seq(m_rng_push_seq, fips_lo_thresh, fips_hi_thresh,
                           bypass_lo_thresh, bypass_hi_thresh, num_invalid_rng_trans);
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid case! (bug in environment)")
      end
    endcase // case (cfg.which_ht_fail)

    fork
      // Start sequences
      m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
      begin
        // Consume entropy via the entropy_data register.
        if (cfg.es_route_sw == MuBi4True) begin
          for (int i = 0; i < (m_csrng_pull_seq.num_trans - 1); i++) begin
            csr_spinwait(.ptr(ral.intr_state.es_entropy_valid), .exp_data(1'b1));
            do_entropy_data_read(.max_bundles(1), .bundles_found(bundles_found));
            `DV_CHECK((bundles_found == 1))
          end
        // Consume entropy via the CSRNG interface.
        end else begin
          m_csrng_pull_seq.start(p_sequencer.csrng_sequencer_h);
        end
      end
    join_any
    // Wait for the es_health_test_failed interrupt.
    csr_spinwait(.ptr(ral.intr_state.es_health_test_failed), .exp_data(1'b1));
    // Expect/Clear interrupt bit for HT failed interrupts.
    check_interrupts(.interrupts((1 << HealthTestFailed)), .check_set(1'b1));
    // To be sure that the ES does not deliver entropy after it has entered an alert state,
    // we wait before we check if we can consume entropy.
    cfg.clk_rst_vif.wait_clks(100);
    // Check if the DUT is in the AlertHang state.
    csr_rd_check(.ptr(ral.main_sm_state.main_sm_state),
                 .compare_value(alert_state));
    // Check if we can consume entropy via the entropy_data register.
    if (cfg.es_route_sw == MuBi4True) begin
      do_entropy_data_read(.max_bundles(1), .bundles_found(bundles_found));
      `DV_CHECK(!bundles_found)
    // Check if we can consume entropy via the CSRNG interface.
    end else begin
      // There should be 1 transaction left for m_csrng_pull_seq.
      `DV_CHECK(cfg.total_seeds_consumed == (m_csrng_pull_seq.num_trans - 1))
      // m_csrng_pull_seq should not be done yet.
      `DV_CHECK(m_csrng_pull_seq.get_sequence_state() != UVM_FINISHED)
      // Reenable the DUT and see if m_csrng_pull_seq finishes after providing
      // valid entropy to the RNG interface.
      disable_dut();
      enable_dut();
      cfg.m_rng_agent_cfg.clear_h_user_data();
      // Provide two windows worth of entropy to make sure m_csrng_pull_seq can finish no
      // matter what the configuration is.
      m_rng_push_seq.num_trans = 3*cfg.dut_cfg.fips_window_size;
      for (int i = 0; i < m_rng_push_seq.num_trans; i++) begin
        rng_val = rng_arr[i%16];
        cfg.m_rng_agent_cfg.add_h_user_data(rng_val);
      end
      m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
      // Make sure m_csrng_pull_seq can now finish.
      `DV_SPINWAIT(wait(m_csrng_pull_seq.get_sequence_state() == UVM_FINISHED);)
      `DV_CHECK(m_csrng_pull_seq.get_sequence_state() == UVM_FINISHED)
      // Ther should have only been one transaction left in m_csrng_pull_seq.
      `DV_CHECK(cfg.total_seeds_consumed == 1)
    end

  endtask // test_es_health_test_failed

  task body();
    // Test es_entropy_valid interrupt
    test_es_entropy_valid();
    // Test es_observe_fifo_ready interrupt
    test_es_observe_fifo_ready();
    // Test es_health_test_failed interrupt
    test_es_health_test_failed();
    // Disable entropy_src
    disable_dut();

  endtask : body

endclass : entropy_src_intr_vseq
