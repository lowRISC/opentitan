// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test entropy_src interrupts

class entropy_src_intr_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_intr_vseq)

  `uvm_object_new

  push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)          m_rng_push_seq;
  push_pull_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)   m_csrng_pull_seq;

  task test_es_observe_fifo_ready();
    // First turn off module_enable to write registers
    csr_wr(.ptr(ral.module_enable), .value(prim_mubi_pkg::MuBi4False));
    // Turn on firmware override mode
    ral.fw_ov_control.fw_ov_mode.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.fw_ov_control));

    // Update obeserve fifo depth threshold
    ral.observe_fifo_thresh.observe_fifo_thresh.set(7'b0000100);
    csr_update(.csr(ral.observe_fifo_thresh));
    // Enable intr_state
    csr_wr(.ptr(ral.intr_enable), .value(32'd15));
    // Turn on module_enable
    csr_wr(.ptr(ral.module_enable), .value(prim_mubi_pkg::MuBi4True));

    // Create and start rng host sequence
    m_rng_push_seq = push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");
    m_rng_push_seq.num_trans = entropy_src_pkg::CSRNG_BUS_WIDTH/entropy_src_pkg::RNG_BUS_WIDTH;
    run_rng_host_seq(m_rng_push_seq);

    // Wait for observe_fifo_ready interrupt
    csr_spinwait(.ptr(ral.intr_state.es_observe_fifo_ready), .exp_data(1'b1));

  endtask // test_es_observe_fifo_ready

  task test_es_entropy_valid();
    // First turn off module_enable to write registers
    csr_wr(.ptr(ral.module_enable), .value(prim_mubi_pkg::MuBi4False));
    // Enable intr_state
    csr_wr(.ptr(ral.intr_enable), .value(32'd15));
    // Turn on module_enable
    csr_wr(.ptr(ral.module_enable), .value(prim_mubi_pkg::MuBi4True));

    // Create and start rng host sequence
    m_rng_push_seq = push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");
    m_rng_push_seq.num_trans = entropy_src_pkg::CSRNG_BUS_WIDTH/entropy_src_pkg::RNG_BUS_WIDTH;
    run_rng_host_seq(m_rng_push_seq);

    // Wait for entropy_valid interrupt
    csr_spinwait(.ptr(ral.intr_state.es_entropy_valid), .exp_data(1'b1));
  endtask // test_es_entropy_valid

  task test_es_health_test_failed();
    bit [15:0]  fips_thresh, bypass_thresh;

    // Create and start rng host sequence
    m_rng_push_seq = push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");
    m_rng_push_seq.num_trans = 2*entropy_src_pkg::CSRNG_BUS_WIDTH/entropy_src_pkg::RNG_BUS_WIDTH;
    // First turn off module_enable to write registers
    csr_wr(.ptr(ral.module_enable), .value(prim_mubi_pkg::MuBi4False));
    // Set a low threshold to introduce ht fails
    fips_thresh = 16'h0008;
    bypass_thresh = 16'h0008;
    case (cfg.which_ht_fail)
      repcnt_ht_fail: begin // Repitition count test
        // Set a low threshold to introduce ht fails
        ral.repcnt_thresholds.fips_thresh.set(fips_thresh);
        ral.repcnt_thresholds.bypass_thresh.set(bypass_thresh);
        csr_update(.csr(ral.repcnt_thresholds));
        // Turn on module_enable
        csr_wr(.ptr(ral.module_enable), .value(prim_mubi_pkg::MuBi4True));
        repcnt_ht_fail_seq(m_rng_push_seq);
      end
      adaptp_ht_fail: begin // Adaptive proportion test
        adaptp_ht_fail_seq(m_rng_push_seq, fips_thresh, bypass_thresh);
      end
      bucket_ht_fail: begin // Bucket test
        bucket_ht_fail_seq(m_rng_push_seq, fips_thresh, bypass_thresh);
      end
      markov_ht_fail: begin // Markov test
        markov_ht_fail_seq(m_rng_push_seq, fips_thresh, bypass_thresh);
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid case! (bug in environment)")
      end
    endcase // case (cfg.which_ht_fail)
    // Start rng host sequence
    m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
    // Wait for es_health_test_failed interrupt
    csr_spinwait(.ptr(ral.intr_state.es_health_test_failed), .exp_data(1'b1));
  endtask // test_es_health_test_failed

  task test_es_fatal_err();
    string        path, path1, path2;
    bit           value1, value2;
    string        path_name, fld_name;
    int           first_index, last_index;
    string        fifo_base_path;
    string        path_exts [4] = {"push", "full", "pop", "not_empty"};
    string        fifo_forced_paths [4];
    bit           fifo_forced_values [4] = {1'b1, 1'b1, 1'b0, 1'b1};
    string        fifo_err_path [2][string];
    bit           fifo_err_value [2][string];

    fifo_err_path[0] = '{"write": "push", "read": "pop", "state": "full"};
    fifo_err_path[1] = '{"write": "full", "read": "not_empty", "state": "not_empty"};
    fifo_err_value[0] = '{"write": 1'b1, "read": 1'b1, "state": 1'b1};
    fifo_err_value[1] = '{"write": 1'b1, "read": 1'b0, "state": 1'b0};

    fld_name = cfg.which_fatal_err.name();
    first_index = find_index("_", fld_name, "first");
    last_index = find_index("_", fld_name, "last");
    fifo_base_path = fld_name.substr(0, last_index-1);

    foreach (path_exts[i]) begin
      fifo_forced_paths[i] = cfg.entropy_src_path_vif.fifo_err_path(fifo_base_path, path_exts[i]);
    end

    // Create and start rng host sequence
    m_rng_push_seq = push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");
    m_rng_push_seq.num_trans = entropy_src_pkg::CSRNG_BUS_WIDTH/entropy_src_pkg::RNG_BUS_WIDTH;
    run_rng_host_seq(m_rng_push_seq);
    cfg.clk_rst_vif.wait_clks(100);

    case (cfg.which_fatal_err) inside
      sfifo_observe_error, sfifo_esrng_error, sfifo_esfinal_error: begin
        path_name = cfg.which_fifo_err.name();

        path1 = cfg.entropy_src_path_vif.fifo_err_path(fifo_base_path,
                                                       fifo_err_path[0][path_name]);
        path2 = cfg.entropy_src_path_vif.fifo_err_path(fifo_base_path,
                                                       fifo_err_path[1][path_name]);
        value1 = fifo_err_value[0][path_name];
        value2 = fifo_err_value[1][path_name];

        if (cfg.which_fatal_err == sfifo_esrng_error && cfg.which_fifo_err == write) begin
          //Turn off assertions
          cfg.entropy_src_assert_if.assert_off_err();
          force_fifo_err_exception(fifo_forced_paths, fifo_forced_values,
                                   ral.intr_state.es_fatal_err, 1'b1);
        end else begin
          force_fifo_err(path1, path2, value1, value2, ral.intr_state.es_fatal_err,1'b1);
        end
      end
      es_ack_sm_error, es_main_sm_error: begin
        path = cfg.entropy_src_path_vif.sm_err_path(fld_name.substr(first_index+1, last_index-1));
        force_path_err(path, 16'b0, ral.intr_state.es_fatal_err, 1'b1);
      end
      es_cntr_error: begin
        case (cfg.which_cntr)
          window_cntr: begin // window counter
            window_cntr_err_test(ral.intr_state.es_fatal_err);
          end
          repcnt_ht_cntr: begin // repcnt ht test counter
            repcnt_ht_cntr_test(m_rng_push_seq, ral.intr_state.es_fatal_err);
          end
          repcnts_ht_cntr: begin // repcnts ht test counter
            repcnts_ht_cntr_test(m_rng_push_seq, ral.intr_state.es_fatal_err);
          end
          adaptp_ht_cntr: begin // adaptive proportion test counter
            adaptp_ht_cntr_test(m_rng_push_seq, ral.intr_state.es_fatal_err);
          end
          bucket_ht_cntr: begin // Bucket test counter
            bucket_ht_cntr_test(m_rng_push_seq, ral.intr_state.es_fatal_err);
          end
          markov_ht_cntr: begin // Markov test counter
            markov_ht_cntr_test(m_rng_push_seq, ral.intr_state.es_fatal_err);
          end
          default: begin
            `uvm_fatal(`gfn, "Invalid case! (bug in environment)")
          end
        endcase // case (cfg.which_cntr)
      end
    endcase // case (cfg.which_fatal_err)
  endtask // test_es_fatal_err

  task body();
    // Turn off fatal alert check
    expect_fatal_alerts = 1'b1;

    // Test es_entropy_valid interrupt
    test_es_entropy_valid();

    // Test es_observe_fifo_ready interrupt
    test_es_observe_fifo_ready();

    // Test es_health_test_failed interrupt
    test_es_health_test_failed();

    // Test es_fatal_err interrupt
    test_es_fatal_err();

    // Disable entropy_src
    csr_wr(.ptr(ral.module_enable), .value(prim_mubi_pkg::MuBi4False));
    // Clear intr_enable
    csr_wr(.ptr(ral.intr_enable), .value(32'd0));
    // Clear intr_state
    check_interrupts(.interrupts(4'b1111), .check_set(1'b1));
    // Make sure intr_state register is cleared
    cfg.clk_rst_vif.wait_clks(100);
    csr_rd_check(.ptr(ral.intr_state), .compare_value(0));

  endtask : body

endclass : entropy_src_intr_vseq
