// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_scoreboard extends cip_base_scoreboard#(
    .CFG_T(entropy_src_env_cfg),
    .RAL_T(entropy_src_reg_block),
    .COV_T(entropy_src_env_cov)
  );

// TODO: Cleanup: remove all prim_mubi_pkg:: namespace identifiers (for consistency)
// As this changes many lines, we will do this cleanup in a separate PR

  `uvm_component_utils(entropy_src_scoreboard)

  virtual entropy_src_cov_if cov_vif;

  // used by collect_entropy to determine the FSMs phase
  int seed_idx             = 0;
  int entropy_data_seeds   = 0;
  int entropy_data_drops   = 0;
  int csrng_seeds          = 0;
  int csrng_drops          = 0;
  int observe_fifo_words   = 0;
  int observe_fifo_drops   = 0;

  bit dut_pipeline_enabled = 0;
  bit fw_ov_sha_enabled    = 0;

  // This scoreboard is not capable of anticipating with single-cycle accuracy whether the observe
  // and entropy data FIFOs are empty.  However, we can note when they have been explicitly cleared
  // and use that to anticipate any alerts that may come about background diable events
  bit fifos_cleared = 1;

  // Queue of seeds for predicting reads to entropy_data CSR
  bit [CSRNG_BUS_WIDTH - 1:0]      entropy_data_q[$];

  // Queue of TL_DW words for predicting outputs of the observe FIFO
  bit [TL_DW - 1:0]                observe_fifo_q[$];

  // Queue of TL_DW words for inserting entropy input the DUT pipeline
  bit [TL_DW - 1:0]                process_fifo_q[$];

  // The most recent candidate seed from entropy_data_q
  // At each TL read the TL data item is compared to the appropriate
  // 32-bit segment of this seed (as determented by seed_tl_read_cnt)
  bit [CSRNG_BUS_WIDTH - 1:0]      tl_best_seed_candidate;

  // The previous output seed.  We need to track this to determine whether to expect "recov_alert"
  bit [CSRNG_BUS_WIDTH - 1:0]      prev_csrng_seed;

  // Number of 32-bit TL reads to the current (active) seed
  // Ranges from 0 (no data read out) to CSRNG_BUS_WIDTH/TL_DW (seed fully read out)
  int                              seed_tl_read_cnt = 0;

  bit [FIPS_CSRNG_BUS_WIDTH - 1:0] fips_csrng_q[$];

  // TODO: Document Initial Conditions for health check.
  // This should make no practical difference, but it is important for successful verification.
  rng_val_t                        prev_rng_val = '0;
  int                              repcnt      [RNG_BUS_WIDTH];
  int                              repcnt_symbol;
  int                              max_repcnt, max_repcnt_symbol;

  // TODO: Document method for clearing alerts in programmer's guide
  // TODO: Add health check failure and clearing to integration tests.
  bit threshold_alert_active = 1'b0;

  // TLM agent fifos
  uvm_tlm_analysis_fifo#(push_pull_item#(.HostDataWidth(FIPS_CSRNG_BUS_WIDTH)))
      csrng_fifo;
  uvm_tlm_analysis_fifo#(push_pull_item#(.HostDataWidth(RNG_BUS_WIDTH)))
      rng_fifo;

  // Enabling, disabling and reset all have some effect in clearing the state of the DUT
  // Due to subleties in timing, the DUT resets the Observe FIFO with a unique delay
  typedef enum int {
    HardReset,
    Disable,
    Enable,
    FIFOClr
  } reset_event_e;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    rng_fifo   = new("rng_fifo", this);
    csrng_fifo = new("csrng_fifo", this);

    if (!uvm_config_db#(virtual entropy_src_cov_if)::get
       (null, "*.env" , "entropy_src_cov_if", cov_vif)) begin
       `uvm_fatal(`gfn, $sformatf("Failed to get entropy_src_cov_if from uvm_config_db"))
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    if (cfg.en_scb) begin
      fork
        process_csrng();
      join_none
    end
  endtask

  // Post simulation statistics reporting
  function void report_phase(uvm_phase phase);
    string fmt, msg;

    fmt = "Seeds read from entropy_data:               %0d";
    msg = $sformatf(fmt, entropy_data_seeds);
    `uvm_info(`gfn, msg, UVM_LOW)

    fmt = "Seeds assumed dropped from entropy_data:    %0d";
    msg = $sformatf(fmt, entropy_data_drops);
    `uvm_info(`gfn, msg, UVM_LOW)

    fmt = "Seeds read from csrng interface:            %0d";
    msg = $sformatf(fmt, csrng_seeds);
    `uvm_info(`gfn, msg, UVM_LOW)

    fmt = "Seeds assumed dropped from csrng interface: %0d";
    msg = $sformatf(fmt, csrng_drops);
    `uvm_info(`gfn, msg, UVM_LOW)

    fmt = "Words read from observe fifo:               %0d";
    msg = $sformatf(fmt, observe_fifo_words);
    `uvm_info(`gfn, msg, UVM_LOW)

    fmt = "Words assumed dropped from observe fifo:    %0d";
    msg = $sformatf(fmt, observe_fifo_drops);
    `uvm_info(`gfn, msg, UVM_LOW)
  endfunction

  //
  // Health check test routines
  //

  function void update_repcnts(rng_val_t rng_val);
    for (int i = 0; i < RNG_BUS_WIDTH; i++) begin
      if (rng_val[i] == prev_rng_val[i]) begin
        repcnt[i]++;
        max_repcnt = (repcnt[i] > max_repcnt) ? repcnt[i] : max_repcnt;
      end else begin
        repcnt[i] = 1;
      end
    end
    if (rng_val == prev_rng_val) begin
      repcnt_symbol++;
    end else begin
      repcnt_symbol = 1;
    end
    prev_rng_val = rng_val;
    max_repcnt_symbol = (repcnt_symbol > max_repcnt_symbol) ? repcnt_symbol : max_repcnt_symbol;
  endfunction

  function int calc_adaptp_test(queue_of_rng_val_t window, output int maxval, output int minval);
    int test_cnt[RNG_BUS_WIDTH];
    int minq[$], maxq[$];
    int result = '0;
    for (int i = 0; i < window.size(); i++) begin
      for (int j = 0; j < RNG_BUS_WIDTH; j++) begin
         test_cnt[j] += window[i][j];
      end
    end
    maxq = test_cnt.max();
    maxval = maxq[0];
    minq = test_cnt.min();
    minval = minq[0];
    return test_cnt.sum();
  endfunction

  function int calc_bucket_test(queue_of_rng_val_t window);
    int bin_count = (1 << RNG_BUS_WIDTH);
    int result[$];

    int buckets [] = new [bin_count];

    for (int i = 0; i < window.size(); i++) begin
      int elem = window[i];
      buckets[elem]++;
    end

    for (int i = 0; i < bin_count; i++) begin
      `uvm_info(`gfn, $sformatf("Bucket test. bin: %01h, value: %02h", i, buckets[i]), UVM_DEBUG)
    end

    result = buckets.max();

    `uvm_info(`gfn, $sformatf("Bucket test. max value: %02h", result[0]), UVM_FULL)

    return result[0];
  endfunction

  function int calc_markov_test(queue_of_rng_val_t window, output int maxval, output int minval);
    int pair_cnt[RNG_BUS_WIDTH];
    int minq[$], maxq[$];
    for (int i = 0; i < window.size(); i += 2) begin
      for (int j = 0; j < RNG_BUS_WIDTH; j++) begin
        bit different = window[i][j] ^ window[i + 1][j];
        pair_cnt[j] += different;
      end
    end
    maxq = pair_cnt.max();
    maxval = maxq[0];
    minq = pair_cnt.min();
    minval = minq[0];
    return pair_cnt.sum();
  endfunction

  function int calc_extht_test(queue_of_rng_val_t window);
    // TODO
    int result = 0;
    return result;
  endfunction

  //
  // Debug tool: make sure that the following helper functions use proper names for health checks.
  //
  function void validate_test_name(string name);
    bit is_valid;
    is_valid = (name == "adaptp_hi") ||
               (name == "adaptp_lo") ||
               (name == "bucket"   ) ||
               (name == "markov_hi") ||
               (name == "markov_lo") ||
               (name == "extht_hi" ) ||
               (name == "extht_lo" ) ||
               (name == "repcnt"   ) ||
               (name == "repcnts"  );
    `DV_CHECK_EQ(is_valid, 1, $sformatf("invalid test name: %s\n", name))
  endfunction

  function bit is_low_test(string name);
    int len = name.len();
    return (name.substr(len - 3, len - 1) == "_lo");
  endfunction

  // Operate on the watermark for a given test, using the mirrored copy of the corresponding
  // watermark register.
  //
  // If the value exceeds (or is less then) the latest watermark value, then update the prediction.
  //
  // Implements predictions for all registers named <test>_watermarks.
  function void update_watermark(string test, bit fips_mode, int value);
    string        watermark_field_name;
    string        watermark_reg_name;
    uvm_reg       watermark_reg;
    uvm_reg_field watermark_field;
    int           watermark_val;
    bit           low_test;
    string        fmt;

    validate_test_name(test);

    // The watermark registers for repcnt, repcnts and bucket tests deviate from the
    // general convention of suppressing the "_hi" suffix for tests that do not have a low
    // threshold.
    if ((test == "repcnt") || (test == "repcnts") || (test == "bucket")) begin
      test = {test, "_hi"};
    end

    watermark_field_name = fips_mode ? "fips_watermark" : "bypass_watermark";
    watermark_reg_name   = $sformatf("%s_watermarks", test);
    watermark_reg        = ral.get_reg_by_name(watermark_reg_name);
    watermark_field      = watermark_reg.get_field_by_name(watermark_field_name);
    watermark_val        = watermark_field.get_mirrored_value();
    low_test             = is_low_test(test);

    if (low_test) begin : low_watermark_check
      if (value < watermark_val) begin
        fmt = "Predicted LO watermark for \"%s\" test (FIPS? %d): %04h";
        `uvm_info(`gfn, $sformatf(fmt, test, fips_mode, value), UVM_HIGH)
        `DV_CHECK_FATAL(watermark_field.predict(.value(value), .kind(UVM_PREDICT_READ)))
      end else begin
        fmt = "LO watermark unchanged for \"%s\" test (FIPS? %d): %04h";
        `uvm_info(`gfn, $sformatf(fmt, test, fips_mode, watermark_val), UVM_HIGH)
      end
    end else begin : high_watermark_check
      if (value > watermark_val) begin
        string fmt;
        fmt = "Predicted HI watermark for \"%s\" test (FIPS? %d): %04h";
        `uvm_info(`gfn, $sformatf(fmt, test, fips_mode, value), UVM_HIGH)
        `DV_CHECK_FATAL(watermark_field.predict(.value(value), .kind(UVM_PREDICT_READ)))
      end else begin
        fmt = "HI watermark unchanged for \"%s\" test (FIPS? %d): %04h";
        `uvm_info(`gfn, $sformatf(fmt, test, fips_mode, watermark_val), UVM_HIGH)
      end
    end : high_watermark_check

  endfunction

  // Compare a particular health check value against the corresponding thresholds.
  // If the health check fails, log the failure and update our predictions for the alert registers.
  //
  // Implements predictions for all registers named:
  // <test>_total_fails
  // alert_fail_counts.<test>_fail_count
  // extht_fail_counts.<test>_fail_count
  //
  // Because failing multiple  tests for a single test only count as one total alert failure
  // this routine does not update alert_summary_fail_counts
  //
  function bit check_threshold(string test, bit fips_mode, int value);
    string        threshold_reg_name;
    string        threshold_field_name;
    string        total_fail_reg_name;
    string        total_fail_field_name;
    string        alert_cnt_reg_name;
    string        alert_cnt_field_name;
    uvm_reg       threshold_reg;
    uvm_reg       total_fail_reg;
    uvm_reg       alert_cnt_reg;
    uvm_reg_field threshold_field;
    uvm_reg_field total_fail_field;
    uvm_reg_field alert_cnt_field;

    int        threshold_val;
    bit [3:0]  alert_cnt;
    int        fail_total;
    bit        continuous_test;
    bit        failure;
    bit        low_test;
    string     fmt, msg;

    validate_test_name(test);
    low_test             = is_low_test(test);
    continuous_test      = (test == "repcnt") || (test == "repcnts");

    // TODO: confirm that the FIPS threshold is the only one that matters for the continuous tests.
    // Having split thresholds doesn't matter for such tests.
    threshold_field_name = (fips_mode || continuous_test) ? "fips_thresh" : "bypass_thresh";
    threshold_reg_name  = $sformatf("%s_thresholds", test);

    total_fail_reg_name = $sformatf("%s_total_fails", test);
    total_fail_field_name = total_fail_reg_name;

    // Most tests have field in the alert_fail_counts register, except extht_fail_counts
    if (test.substr(0, 5) == "extht_") begin
      alert_cnt_reg_name = "extht_fail_counts";
    end else begin
      alert_cnt_reg_name = "alert_fail_counts";
    end
    alert_cnt_field_name = $sformatf("%s_fail_count", test);

    threshold_reg    = ral.get_reg_by_name(threshold_reg_name);
    threshold_field  = threshold_reg.get_field_by_name(threshold_field_name);

    total_fail_reg   = ral.get_reg_by_name(total_fail_reg_name);
    total_fail_field = total_fail_reg.get_field_by_name(total_fail_field_name);

    alert_cnt_reg    = ral.get_reg_by_name(alert_cnt_reg_name);
    alert_cnt_field  = alert_cnt_reg.get_field_by_name(alert_cnt_field_name);

    threshold_val = threshold_field.get_mirrored_value();

    failure = (low_test && value < threshold_val) || (!low_test && value > threshold_val);

    fail_total = total_fail_field.get_mirrored_value();
    alert_cnt  =  alert_cnt_field.get_mirrored_value();

    if (failure) begin
      // Update the predicted failure counters, noting that the DUT will not let these overflow
      alert_cnt  += (&alert_cnt)  ? 0 : 1;
      fail_total += (&fail_total) ? 0 : 1;
    end

    fmt = "Threshold for \"%s\" test (FIPS? %d): %04h";
    `uvm_info(`gfn, $sformatf(fmt, test, fips_mode, threshold_val), UVM_HIGH)

    fmt = "Observed value for \"%s\" test (FIPS? %d): %04h, %s";
    `uvm_info(`gfn, $sformatf(fmt, test, fips_mode, value, failure ? "FAIL" : "PASS"), UVM_HIGH)

    fmt = "Previous alert cnt reg: %08h";
    msg = $sformatf(fmt, alert_cnt_reg.get_mirrored_value());
    `uvm_info(`gfn, msg, UVM_FULL)

    `DV_CHECK_FATAL(total_fail_field.predict(.value(fail_total), .kind(UVM_PREDICT_DIRECT)))
    `DV_CHECK_FATAL( alert_cnt_field.predict(.value( alert_cnt), .kind(UVM_PREDICT_DIRECT)))

    fmt = "Predicted alert cnt for \"%s\" test (FIPS? %d): %04h";
    msg = $sformatf(fmt, test, fips_mode, alert_cnt_field.get_mirrored_value());
    `uvm_info(`gfn, msg, UVM_HIGH)

    fmt = "Entire alert cnt reg: %08h";
    msg = $sformatf(fmt, alert_cnt_reg.get_mirrored_value());
    `uvm_info(`gfn, msg, UVM_FULL)

    fmt = "Predicted fail cnt for \"%s\" test (FIPS? %d): %01h";
    msg = $sformatf(fmt, test, fips_mode, total_fail_field.get_mirrored_value());
    `uvm_info(`gfn, msg, UVM_HIGH)

    return failure;

  endfunction

  function bit evaluate_adaptp_test(queue_of_rng_val_t window, bit fips_mode);
    int value, minval, maxval;
    bit fail_hi, fail_lo;
    bit total_scope;
    total_scope = (ral.conf.threshold_scope.get_mirrored_value() == prim_mubi_pkg::MuBi4True);

    value = calc_adaptp_test(window, maxval, minval);

    update_watermark("adaptp_lo", fips_mode, total_scope ? value : minval);
    update_watermark("adaptp_hi", fips_mode, total_scope ? value : maxval);

    fail_lo = check_threshold("adaptp_lo", fips_mode, total_scope ? value : minval);
    fail_hi = check_threshold("adaptp_hi", fips_mode, total_scope ? value : maxval);

    return (fail_hi || fail_lo);
  endfunction

  function bit evaluate_bucket_test(queue_of_rng_val_t window, bit fips_mode);
    int value;
    bit fail;

    value = calc_bucket_test(window);

    update_watermark("bucket", fips_mode, value);

    fail = check_threshold("bucket", fips_mode, value);

    return fail;
  endfunction

  function bit evaluate_markov_test(queue_of_rng_val_t window, bit fips_mode);
    int value, minval, maxval;
    bit fail_hi, fail_lo;
    bit total_scope;
    total_scope = (ral.conf.threshold_scope.get_mirrored_value() == prim_mubi_pkg::MuBi4True);

    value = calc_markov_test(window, maxval, minval);

    update_watermark("markov_lo", fips_mode, total_scope ? value : minval);
    update_watermark("markov_hi", fips_mode, total_scope ? value : maxval);

    fail_lo = check_threshold("markov_lo", fips_mode, total_scope ? value : minval);
    fail_hi = check_threshold("markov_hi", fips_mode, total_scope ? value : maxval);

    return (fail_hi || fail_lo);
  endfunction

  function evaluate_external_ht(queue_of_rng_val_t window, bit fips_mode);
    int value;
    bit fail_hi, fail_lo;

    value = calc_extht_test(window);

    update_watermark("extht_lo", fips_mode, value);
    update_watermark("extht_hi", fips_mode, value);

    fail_lo = check_threshold("extht_lo", fips_mode, value);
    fail_hi = check_threshold("extht_hi", fips_mode, value);

    return (fail_hi || fail_lo);
  endfunction

  // The repetition counts are always running
  function bit evaluate_repcnt_test(bit fips_mode);
    int value;
    bit fail;

    value = max_repcnt;

    update_watermark("repcnt", fips_mode, value);

    fail = check_threshold("repcnt", fips_mode, value);

    return fail;
  endfunction

  function bit evaluate_repcnt_symbol_test(bit fips_mode);
    int value;
    bit fail;

    value = max_repcnt_symbol;

    update_watermark("repcnts", fips_mode, value);

    fail = check_threshold("repcnts", fips_mode, value);

    return fail;
  endfunction

  function bit health_check_rng_data(queue_of_rng_val_t window, bit fips_mode, bit fw_ov_insert);
    int failcnt = 0, failcnt_fatal = 0;
    bit failure = 0;
    uvm_reg       alert_summary_reg   = ral.get_reg_by_name("alert_summary_fail_counts");
    uvm_reg_field alert_summary_field = alert_summary_reg.get_field_by_name("any_fail_count");
    uvm_reg       alert_fail_reg   = ral.get_reg_by_name("alert_fail_counts");
    uvm_reg       extht_fail_reg   = ral.get_reg_by_name("extht_fail_counts");
    uvm_reg       alert_threshold_reg = ral.get_reg_by_name("alert_threshold");
    // TODO: Confirm that an alert is triggered when (alert_threshold != alert_threshold_inv)
    uvm_reg_field alert_threshold_field = alert_threshold_reg.get_field_by_name("alert_threshold");
    string        fmt;
    int           any_fail_count_regval;
    int           alert_threshold;

    failcnt_fatal += evaluate_repcnt_test(fips_mode);
    failcnt_fatal += evaluate_repcnt_symbol_test(fips_mode);
    failcnt += evaluate_adaptp_test(window, fips_mode);
    failcnt += evaluate_bucket_test(window, fips_mode);
    failcnt += evaluate_markov_test(window, fips_mode);
    failcnt += evaluate_external_ht(window, fips_mode);

    failure = (failcnt != 0  || failcnt_fatal != 0);

    // TODO: If an alert is anticipated, we should check that (if necessary) this seed is
    // stopped and no others are allowed to progress.
    alert_threshold = alert_threshold_field.get_mirrored_value();

    any_fail_count_regval = alert_summary_field.get_mirrored_value();
    if (failure) begin : test_failure
      any_fail_count_regval++;
      if (any_fail_count_regval >= alert_threshold) begin
        if(!fw_ov_insert && !threshold_alert_active) begin
          fmt = "New alert anticpated! Fail count (%01d) >= threshold (%01d)";
          threshold_alert_active = 1;
          set_exp_alert(.alert_name("recov_alert"), .is_fatal(0), .max_delay(cfg.alert_max_delay));
        end else begin
          fmt = "Alert already signalled:  Fail count (%01d) >= threshold (%01d)";
        end
        `uvm_info(`gfn, $sformatf(fmt, any_fail_count_regval, alert_threshold), UVM_HIGH)
      end else begin
        fmt = "No alert anticpated. fail count (%01d) < threshold (%01d)";
        `uvm_info(`gfn, $sformatf(fmt, any_fail_count_regval, alert_threshold), UVM_HIGH)
      end
    end else begin : no_test_failure
      if (!threshold_alert_active) begin
        any_fail_count_regval = 0;
        // Now we know that all tests have passed we can clear the failure counts
        `DV_CHECK_FATAL(alert_fail_reg.predict(.value({TL_DW{1'b0}}), .kind(UVM_PREDICT_DIRECT)))
      end else begin
        fmt = "Alert state persists: Fail count (%01d) >= threshold (%01d)";
        `uvm_info(`gfn, $sformatf(fmt, any_fail_count_regval, alert_threshold), UVM_HIGH)
      end
    end : no_test_failure

   `DV_CHECK_FATAL(alert_summary_field.predict(.value(any_fail_count_regval),
                                               .kind(UVM_PREDICT_DIRECT)))

    fmt = "Predicted alert cnt for all tests (FIPS? %d): %04h";
    `uvm_info(`gfn, $sformatf(fmt, fips_mode, any_fail_count_regval), UVM_HIGH)
    return failure;
  endfunction

  //
  // Helper functions for process_entropy_data_csr_access
  //

  function bit try_seed_tl(input bit [CSRNG_BUS_WIDTH - 1:0] new_candidate,
                           input bit [TL_DW - 1:0] tl_data,
                           output bit [TL_DW - 1:0] tl_prediction);
    bit [CSRNG_BUS_WIDTH - 1:0] mask, new_seed_masked, best_seed_masked;
    bit matches_prev_reads;
    bit matches_tl_data;
    string fmt;

    mask = '0;

    for(int i = 0; i < seed_tl_read_cnt; i++) begin
      mask[i * TL_DW +: TL_DW] = {TL_DW{1'b1}};
    end
    new_seed_masked = (new_candidate & mask);
    best_seed_masked = (tl_best_seed_candidate & mask);
    matches_prev_reads = (best_seed_masked == new_seed_masked);

    if (matches_prev_reads) begin
      // Only log this if the new seed is different from the previous best:
      if (new_candidate != tl_best_seed_candidate) begin
        string fmt = "Found another match candidate after %01d total dropped seeds";
       `uvm_info(`gfn, $sformatf(fmt, entropy_data_drops), UVM_HIGH)
      end
    end else begin
      `uvm_info(`gfn, "New candidate seed does not match previous segments", UVM_HIGH)
      fmt = "New seed: %096h, Best seed: %096h";
      // In the log mask out portions that have not been compared yet, for contrast
      `uvm_info(`gfn, $sformatf(fmt, new_seed_masked, best_seed_masked), UVM_HIGH)
       return 0;
    end

    tl_prediction = new_candidate[TL_DW * seed_tl_read_cnt +: TL_DW];
    matches_tl_data = (tl_prediction == tl_data);

    if (tl_prediction == tl_data) begin
      tl_best_seed_candidate = new_candidate;
      fmt = "Seed matches TL data after %d TL reads";
      `uvm_info(`gfn, $sformatf(fmt, seed_tl_read_cnt+1), UVM_HIGH)
      return 1;
    end else begin
      fmt = "TL DATA (%08h) does not match predicted seed segment (%08h)";
      `uvm_info(`gfn, $sformatf(fmt, tl_data, tl_prediction), UVM_HIGH)
      return 0;
    end

  endfunction

  // Helper routine for process_tl_access
  //
  // Since the DUT may, by design, internally drop data, it is not sufficient to check against
  // one seed, we compare TL data values against all available seeds.
  // If no match is found then the access is in error.
  //
  task process_entropy_data_csr_access(tl_seq_item item, uvm_reg csr);

    bit [TL_DW - 1:0] ed_pred_data;
    bit               match_found;
    bit entropy_data_reg_enable;
    bit module_enabled;
    entropy_data_reg_enable = (cfg.otp_en_es_fw_read == MuBi8True) &&
                              (ral.conf.entropy_data_reg_enable.get_mirrored_value() == MuBi4True);

    module_enabled = (ral.module_enable.module_enable.get_mirrored_value() == MuBi4True);

    match_found = 0;

    if(!entropy_data_reg_enable || !module_enabled) begin
      // ignore the contents of the entropy_data fifo.
      `DV_CHECK_FATAL(csr.predict(.value({TL_DW{1'b0}}), .kind(UVM_PREDICT_READ)))
      match_found = 1;
    end else begin
      while (entropy_data_q.size() > 0) begin : seed_trial_loop
        bit [TL_DW - 1:0] prediction;
        `uvm_info(`gfn, $sformatf("seed_tl_read_cnt: %01d", seed_tl_read_cnt), UVM_FULL)
        match_found = try_seed_tl(entropy_data_q[0], item.d_data, prediction);
        if (match_found) begin
          bit full_seed_found = 0;
          `DV_CHECK_FATAL(csr.predict(.value(prediction), .kind(UVM_PREDICT_READ)))
          seed_tl_read_cnt++;
          if (seed_tl_read_cnt == CSRNG_BUS_WIDTH / TL_DW) begin
            full_seed_found = 1;
            seed_tl_read_cnt = 0;
            entropy_data_q.pop_front();
            entropy_data_seeds++;
          end else if (seed_tl_read_cnt > CSRNG_BUS_WIDTH / TL_DW) begin
            `uvm_error(`gfn, "testbench error: too many segments read from candidate seed")
          end
          cov_vif.cg_seed_output_csr_sample(
              ral.conf.fips_enable.get_mirrored_value(),
              ral.conf.threshold_scope.get_mirrored_value(),
              ral.conf.rng_bit_enable.get_mirrored_value(),
              ral.conf.rng_bit_sel.get_mirrored_value(),
              ral.entropy_control.es_route.get_mirrored_value(),
              ral.entropy_control.es_type.get_mirrored_value(),
              ral.conf.entropy_data_reg_enable.get_mirrored_value(),
              cfg.otp_en_es_fw_read,
              ral.fw_ov_control.fw_ov_mode.get_mirrored_value(),
              ral.fw_ov_control.fw_ov_entropy_insert.get_mirrored_value(),
              full_seed_found
          );
          break;
        end else begin
          entropy_data_q.pop_front();
          entropy_data_drops++;
        end
      end : seed_trial_loop
    end

    `DV_CHECK_EQ_FATAL(match_found, 1,
                       "All candidate seeds have been checked.  ENTROPY_DATA does not match")
  endtask

  function void clear_ht_stat_predictions();
    string stat_regs [] = '{
        "repcnt_hi_watermarks", "repcnts_hi_watermarks", "adaptp_hi_watermarks",
        "adaptp_lo_watermarks", "extht_hi_watermarks", "extht_lo_watermarks",
        "bucket_hi_watermarks", "markov_hi_watermarks", "markov_lo_watermarks",
        "repcnt_total_fails", "repcnts_total_fails", "adaptp_hi_total_fails",
        "adaptp_lo_total_fails", "bucket_total_fails", "markov_hi_total_fails",
        "markov_lo_total_fails", "extht_hi_total_fails", "extht_lo_total_fails",
        "alert_summary_fail_counts", "alert_fail_counts", "extht_fail_counts"
    };
    foreach (stat_regs[i]) begin
      uvm_reg csr = ral.get_reg_by_name(stat_regs[i]);
      void'(csr.predict(.value(csr.get_reset()), .kind(UVM_PREDICT_READ)));
    end
  endfunction

  // Clear all relevant prediction variables for
  // Reset, disable, enable and (delayed) FIFOClr reset events.
  function void handle_disable_reset(reset_event_e rst_type);
    if (rst_type == Enable) begin
      clear_ht_stat_predictions();
    end
    // Internal entropy stores are cleared on Disable and HardReset events
    if( rst_type == Disable || rst_type == HardReset ) begin
      fips_csrng_q.delete();
      process_fifo_q.delete();
    end
    if (rst_type == FIFOClr) begin
      observe_fifo_q.delete();
      entropy_data_q.delete();
    end

    // reset all other statistics
    threshold_alert_active = 0;
    seed_idx = 0;
    seed_tl_read_cnt = 0;
    for (int i = 0; i < RNG_BUS_WIDTH; i++) begin
      repcnt[i]       = 0;
    end
    repcnt_symbol     = 0;
    max_repcnt        = 0;
    max_repcnt_symbol = 0;
    rng_fifo.flush();
    // TODO: should we flush the CSRNG fifo?
    //csrng_fifo.flush();

    `uvm_info(`gfn, $sformatf("%s Detected", rst_type.name), UVM_MEDIUM)
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    // TODO: Add conditioning prediction, still TBD in design
    bit do_read_check       = 1'b1;
    bit write               = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
    string msg;

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    if (channel == AddrChannel) begin
      // if incoming access is a write to a valid csr, then make updates right away
      if (write) begin
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
        // Special handling for registers with broader impacts
        case (csr.get_name())
          "module_enable": begin
            bit do_disable, do_enable;
            uvm_reg_field enable_field = csr.get_field_by_name("module_enable");
            prim_mubi_pkg::mubi4_t enable_mubi = enable_field.get_mirrored_value();
            // TODO: integrate this with invalid MuBi checks
            do_disable = (enable_mubi == prim_mubi_pkg::MuBi4False);
            do_enable  = (enable_mubi == prim_mubi_pkg::MuBi4True);
            if (do_enable && !dut_pipeline_enabled) begin
              dut_pipeline_enabled = 1;
              fork
                begin
                  handle_disable_reset(Enable);
                  fifos_cleared = 0;
                  collect_entropy();
                  handle_disable_reset(Disable);
                end
              join_none
            end
            if (do_disable && dut_pipeline_enabled) begin
              fork : background_process
                begin
                  // The DUT does not immediately turn off the RNG input
                  // We wait a few cycles to let any last couple RNG
                  // samples come into the dut (so we know to delete them
                  // from our model of the DUT);
                  cfg.clk_rst_vif.wait_clks(cfg.tlul_to_rng_disable_delay);
                  dut_pipeline_enabled = 0;
                end
                begin
                  cfg.clk_rst_vif.wait_clks(cfg.tlul_to_fifo_clr_delay);
                  handle_disable_reset(FIFOClr);
                  fifos_cleared = 1;
                end
              join_none : background_process
            end
          end
          "fw_ov_sha3_start": begin
            // The fw_ov_sha3_start field triggers the internal processing of SHA data
            mubi4_t start_mubi  = csr.get_field_by_name("fw_ov_insert_start").get_mirrored_value();
            bit fips_enabled    = ral.conf.fips_enable.get_mirrored_value() == MuBi4True;
            bit es_route        = ral.entropy_control.es_route.get_mirrored_value() == MuBi4True;
            bit es_type         = ral.entropy_control.es_type.get_mirrored_value() == MuBi4True;
            bit is_fips_mode    = fips_enabled && !(es_route && es_type);
            bit fw_ov_mode      = (cfg.otp_en_es_fw_read == MuBi8True) &&
                                  (ral.fw_ov_control.fw_ov_mode.get_mirrored_value() == MuBi4True);
            mubi4_t insert_mubi = ral.fw_ov_control.fw_ov_entropy_insert.get_mirrored_value();
            bit fw_ov_insert    = fw_ov_mode && (insert_mubi == MuBi4True);
            bit do_disable_sha  = fw_ov_sha_enabled && (start_mubi == MuBi4False);
            // Disabling the fw_ov_sha3_start field triggers the conditioner, but only
            // if the DUT is configured properly.
            if (dut_pipeline_enabled && is_fips_mode && fw_ov_insert && do_disable_sha) begin
              `uvm_info(`gfn, "SHA3 disabled for FW_OV", UVM_HIGH)
              package_and_release_entropy();
            end
            fw_ov_sha_enabled = (start_mubi == MuBi4True);
            if (fw_ov_sha_enabled && fw_ov_insert) begin
              `uvm_info(`gfn, "SHA3 enabled for FW_OV", UVM_HIGH)
            end
          end
          "fw_ov_wr_data": begin
            bit fips_enabled    = ral.conf.fips_enable.get_mirrored_value() == MuBi4True;
            bit es_route        = ral.entropy_control.es_route.get_mirrored_value() == MuBi4True;
            bit es_type         = ral.entropy_control.es_type.get_mirrored_value() == MuBi4True;
            bit is_fips_mode    = fips_enabled && !(es_route && es_type);

            bit fw_ov_entropy_insert =
                (cfg.otp_en_es_fw_over == MuBi8True) &&
                (ral.fw_ov_control.fw_ov_mode.get_mirrored_value() == MuBi4True) &&
                (ral.fw_ov_control.fw_ov_entropy_insert.get_mirrored_value() == MuBi4True);
            msg = $sformatf("fw_ov_wr_data captured: 0x%08x", item.a_data);
            `uvm_info(`gfn, msg, UVM_FULL)

            if (dut_pipeline_enabled && fw_ov_entropy_insert) begin
              msg = $sformatf("Inserting word 0x%08x into pipeline", item.a_data);
              `uvm_info(`gfn, msg, UVM_MEDIUM)
              process_fifo_q.push_back(item.a_data);
              // In bypass mode, data is automatically released when a full seed is acquired
              if (!is_fips_mode && process_fifo_q.size() == (CSRNG_BUS_WIDTH / TL_DW)) begin
                package_and_release_entropy();
              end
            end
          end
          default: begin
          end
        endcase
      end
    end
    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        // TODO
        do_read_check = 1'b0;
      end
      "intr_enable": begin
      end
      "intr_test": begin
      end
      "me_regwen": begin
      end
      "sw_regupd": begin
      end
      "regwen": begin
      end
      "module_enable": begin
      end
      "conf": begin
      end
      "rev": begin
      end
      "rate": begin
      end
      "entropy_control": begin
      end
      "entropy_data": begin
      end
      "health_test_windows": begin
      end
      "repcnt_thresholds": begin
      end
      "repcnts_thresholds": begin
      end
      "adaptp_hi_thresholds": begin
      end
      "adaptp_lo_thresholds": begin
      end
      "bucket_thresholds": begin
      end
      "markov_hi_thresholds": begin
      end
      "markov_lo_thresholds": begin
      end
      "repcnt_hi_watermarks": begin
        // TODO: KNOWN ISSUE: pending resolution to #9819
        do_read_check = 1'b0;
      end
      "repcnts_hi_watermarks": begin
        // TODO: KNOWN ISSUE: pending resolution to #9819
        do_read_check = 1'b0;
      end
      "adaptp_hi_watermarks": begin
      end
      "adaptp_lo_watermarks": begin
      end
      "bucket_hi_watermarks": begin
      end
      "markov_hi_watermarks": begin
      end
      "markov_lo_watermarks": begin
      end
      "extht_hi_watermarks": begin
      end
      "extht_lo_watermarks": begin
      end
      "repcnt_total_fails": begin
      end
      "repcnts_total_fails": begin
      end
      "adaptp_hi_total_fails": begin
      end
      "adaptp_lo_total_fails": begin
      end
      "bucket_total_fails": begin
      end
      "markov_hi_total_fails": begin
      end
      "markov_lo_total_fails": begin
      end
      "extht_hi_total_fails": begin
      end
      "extht_lo_total_fails": begin
      end
      "alert_threshold": begin
      end
      "alert_summary_fail_counts": begin
      end
      "alert_fail_counts": begin
      end
      "extht_fail_counts": begin
      end
      "fw_ov_control": begin
      end
      "fw_ov_sha3_start": begin
      end
      "fw_ov_rd_data": begin
      end
      "fw_ov_wr_data": begin
      end
      "observe_fifo_thresh": begin
      end
      "debug_status": begin
      end
      "recov_alert_sts": begin
        do_read_check = 1'b0;
      end
      "err_code": begin
      end
      "err_code_check": begin
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check is set, then check mirrored_value against item.d_data
    if (!write && channel == DataChannel) begin
      if (do_read_check) begin
        case (csr.get_name())
          "entropy_data": begin
            // TODO(Enhancement): Ideally the scoreboard would have monitor access to the
            // internal state of the entropy_data and observe FIFOs.  At this point however
            // the environment can run satisfactorily by checking whether the FIFOs have
            // been cleared in a disable event.
            if (fifos_cleared) begin
              `DV_CHECK_FATAL(csr.predict(.value('0), .kind(UVM_PREDICT_READ)))
            end else begin
              process_entropy_data_csr_access(item, csr);
            end
          end
          "fw_ov_rd_data": begin
            if (fifos_cleared) begin
              `DV_CHECK_FATAL(csr.predict(.value('0), .kind(UVM_PREDICT_READ)))
            end else begin
              process_observe_fifo_csr_access(item, csr);
            end
          end
        endcase

        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
    end
  endtask

  function bit [FIPS_BUS_WIDTH - 1:0] get_fips_compliance(
      bit [FIPS_CSRNG_BUS_WIDTH - 1:0] fips_csrng);
    return fips_csrng[CSRNG_BUS_WIDTH +: FIPS_BUS_WIDTH];
  endfunction

  function bit [CSRNG_BUS_WIDTH - 1:0] get_csrng_seed(bit [FIPS_CSRNG_BUS_WIDTH - 1:0] fips_csrng);
    return fips_csrng[0 +: CSRNG_BUS_WIDTH];
  endfunction

  // Note: this routine is destructive in that it empties the input argument
  function bit [FIPS_CSRNG_BUS_WIDTH - 1:0] predict_fips_csrng();
    bit [FIPS_CSRNG_BUS_WIDTH - 1:0] fips_csrng_data;
    bit [CSRNG_BUS_WIDTH - 1:0]      csrng_data;
    bit [FIPS_BUS_WIDTH - 1:0]       fips_data;
    entropy_phase_e                  dut_phase;
    bit                              predict_conditioned;
    prim_mubi_pkg::mubi4_t           rng_single_bit;

    int                              sample_frames;
    int                              pass_cnt_threshold;
    int                              pass_cnt;
    bit                              fw_ov_insert;

    bit                              route_sw;
    bit                              sw_bypass;
    bit                              fips_enable;
    bit                              is_fips_mode;

    route_sw    = (ral.entropy_control.es_route.get_mirrored_value() == MuBi4True);
    sw_bypass   = (ral.entropy_control.es_type.get_mirrored_value()  == MuBi4True);
    fips_enable = (ral.conf.fips_enable.get_mirrored_value()         == MuBi4True);

    is_fips_mode = fips_enable && !(route_sw && sw_bypass);

    fw_ov_insert = (cfg.otp_en_es_fw_over == MuBi8True) &&
                   (ral.fw_ov_control.fw_ov_mode.get_mirrored_value() == MuBi4True) &&
                   (ral.fw_ov_control.fw_ov_entropy_insert.get_mirrored_value() == MuBi4True);

    rng_single_bit = ral.conf.rng_bit_enable.get_mirrored_value();

    dut_phase = convert_seed_idx_to_phase(seed_idx,
                                          is_fips_mode,
                                          fw_ov_insert);

    sample_frames = process_fifo_q.size();

    `uvm_info(`gfn, $sformatf("processing %01d 32-bit frames", sample_frames), UVM_FULL)

    predict_conditioned = !((route_sw && sw_bypass) || (dut_phase == BOOT));

    fips_data = predict_conditioned && (rng_single_bit == prim_mubi_pkg::MuBi4False);

    if (predict_conditioned) begin
      localparam int BytesPerWord = TL_DW / 8;

      bit [7:0] sha_msg[];
      bit [7:0] sha_digest[CSRNG_BUS_WIDTH / 8];
      longint msg_len = 0;

      sha_msg = new[process_fifo_q.size() * BytesPerWord];

      // The DUT's SHA engine takes data in 64 bit chunks, whereas the input is 32-bit wide.
      // Any unpaired 32-bit chunks will be left in the pipeline.
      while (process_fifo_q.size() > 1) begin
        bit [31:0] word    = '0;
        bit [7:0] sha_byte = '0;
        for (int j = 0; j < 2; j++) begin
          word = process_fifo_q.pop_front();
          for (int i = 0; i < BytesPerWord; i++) begin
            sha_byte = word[ 0 +: 8];
            word     = word >> 8;
            `uvm_info(`gfn, $sformatf("msglen: %04h, byte: %02h", msg_len, sha_byte), UVM_FULL)
            sha_msg[msg_len] = sha_byte;
            msg_len++;
          end
        end
      end

      `uvm_info(`gfn, $sformatf("DIGESTION COMMENCING of %d bytes", msg_len), UVM_FULL)

      digestpp_dpi_pkg::c_dpi_sha3_384(sha_msg, msg_len, sha_digest);

      `uvm_info(`gfn, "DIGESTING COMPLETE", UVM_FULL)

      csrng_data = '0;
      for(int i = 0; i < CSRNG_BUS_WIDTH / 8; i++) begin
        bit [7:0] sha_byte = sha_digest[i];

        `uvm_info(`gfn, $sformatf("repacking: %02d", i), UVM_FULL)

        csrng_data = (csrng_data >> 8) | (sha_byte << (CSRNG_BUS_WIDTH - 8));
      end
      `uvm_info(`gfn, $sformatf("Conditioned data: %096h", csrng_data), UVM_HIGH)

    end else begin

      while (process_fifo_q.size() > 0) begin
        bit [TL_DW - 1:0] word = process_fifo_q.pop_front();
        string fmt             = "sample size: %01d, last elem.: %01h";
        `uvm_info(`gfn, $sformatf(fmt, process_fifo_q.size()+1, word), UVM_FULL)

        csrng_data = csrng_data >> TL_DW;
        csrng_data[CSRNG_BUS_WIDTH - TL_DW +: TL_DW] = word;
      end
      `uvm_info(`gfn, $sformatf("Unconditioned data: %096h", csrng_data), UVM_HIGH)
    end

    fips_csrng_data = {fips_data, csrng_data};

    return fips_csrng_data;
  endfunction

  // Wait on the RNG queue for rng sequence items
  //
  // If bit selection is enabled, wait for RNG_BUS_WIDTH items. Otherwise, return after one item.
  // If at any point dut_pipeline_enabled is deasserted, halt and assert disable_detected.
  task wait_rng_queue(output rng_val_t val, output bit disable_detected);
    push_pull_item#(.HostDataWidth(RNG_BUS_WIDTH))  rng_item;
    bit bit_sel_enable = (cfg.rng_bit_enable == prim_mubi_pkg::MuBi4True);
    int n_items        = bit_sel_enable ? RNG_BUS_WIDTH : 1;
    disable_detected   = 0;

    if (!dut_pipeline_enabled) begin
      wait(dut_pipeline_enabled);
      `uvm_info(`gfn, "Enable detected", UVM_MEDIUM);
    end
    for (int i = 0; i < n_items; i++) begin : rng_loop
      fork : isolation_fork
        begin
          fork
            rng_fifo.get(rng_item);
            begin
              wait(!dut_pipeline_enabled);
              `uvm_info(`gfn, "Disable detected", UVM_MEDIUM);
            end
          join_any
          disable fork;
        end
      join : isolation_fork
      if (!dut_pipeline_enabled) begin
        `uvm_info(`gfn, "Flushing data on disable", UVM_MEDIUM)
        disable_detected = 1;
        break;
      end
      if (bit_sel_enable) begin
        val[i] = rng_item.h_data[cfg.rng_bit_sel];
      end else begin
        val    = rng_item.h_data;
      end
    end : rng_loop
  endtask

  task collect_entropy();

    bit [15:0]                window_size;
    entropy_phase_e           dut_fsm_phase;
    rng_val_t                 rng_val;
    queue_of_rng_val_t        window;
    int                       window_rng_frames;
    int                       pass_requirement, pass_cnt;
    int                       repack_idx = 0;
    bit [TL_DW - 1:0]         repacked_entropy;
    bit                       ht_fips_mode;
    bit                       disable_detected;
    bit                       fw_ov_insert;
    bit                       is_fips_mode;
    localparam int RngPerTlDw = TL_DW / RNG_BUS_WIDTH;
    bit                       fips_enable, es_route, es_type;

    fips_enable = (ral.conf.fips_enable.get_mirrored_value()         == MuBi4True);
    es_route    = (ral.entropy_control.es_route.get_mirrored_value() == MuBi4True);
    es_type     = (ral.entropy_control.es_type.get_mirrored_value()  == MuBi4True);

    is_fips_mode  = fips_enable && !(es_route && es_type);

    fw_ov_insert = (cfg.otp_en_es_fw_over == MuBi8True) &&
                   (ral.fw_ov_control.fw_ov_mode.get_mirrored_value() == MuBi4True) &&
                   (ral.fw_ov_control.fw_ov_entropy_insert.get_mirrored_value() == MuBi4True);

    pass_cnt = 0;

    window.delete();

    forever begin : collect_entropy_loop

      `uvm_info(`gfn, $sformatf("SEED_IDX: %01d", seed_idx), UVM_FULL)

      dut_fsm_phase = convert_seed_idx_to_phase(seed_idx, is_fips_mode, fw_ov_insert);

      case (dut_fsm_phase)
        BOOT: begin
          pass_requirement = 1;
          ht_fips_mode     = 0;
        end
        STARTUP: begin
          pass_requirement = 2;
          ht_fips_mode     = 1;
        end
        CONTINUOUS: begin
          pass_requirement = 1;
          ht_fips_mode     = 1;
        end
        HALTED: begin
          // When in the post-boot, halted state the DUT will continue to monitor health checks, but
          // not output CSRNG data or data to the TL ENTROPY_DATA register.
          // In this cass the pass_requirement and ht_fips_mode values don't mean anything
          pass_requirement = 0;
          ht_fips_mode     = 0;
        end
        default: begin
          `uvm_fatal(`gfn, "Invalid predicted dut state (bug in environment)")
        end
      endcase

      `uvm_info(`gfn, $sformatf("phase: %s\n", dut_fsm_phase.name), UVM_HIGH)

      window_size = rng_window_size(seed_idx, is_fips_mode,
                                    fw_ov_insert, cfg.fips_window_size);

      `uvm_info(`gfn, $sformatf("window_size: %08d\n", window_size), UVM_HIGH)

      // Note on RNG bit enable and window frame count:
      // When rng_bit_enable is selected, the function below repacks the data so that
      // the selected bit fills a whole frame.
      // This mirrors the DUT's behavior of repacking the data before the health checks
      //
      // Thus the number of (repacked) window frames is the same regardless of whether
      // the bit select is enabled.

      window_rng_frames = window_size / RNG_BUS_WIDTH;

      window.delete();
      // Should the next window be added to the previous SHA3 message?
      // In boot or bypass mode the answer is "no"

      while (window.size() < window_rng_frames) begin
        string fmt;
        wait_rng_queue(rng_val, disable_detected);

        if (disable_detected) begin
          // Exit this task.
          return;
        end else begin
          // Add this data to health check windows
          window.push_back(rng_val);

          // Pack this data for redistribution
          repacked_entropy = {rng_val,
                              repacked_entropy[RNG_BUS_WIDTH +: (TL_DW - RNG_BUS_WIDTH)]};
          repack_idx++;
          `uvm_info(`gfn, $sformatf("repack_idx: %0d", repack_idx), UVM_DEBUG)
          if (repack_idx == RngPerTlDw) begin
            repack_idx = 0;
            observe_fifo_q.push_back(repacked_entropy);
            if (!fw_ov_insert) begin
              process_fifo_q.push_back(repacked_entropy);
            end
          end

          fmt = "RNG element: %0x, idx: %0d";
          `uvm_info(`gfn, $sformatf(fmt, rng_val, window.size()), UVM_DEBUG)

          // Update the repetition counts, which are updated continuously.
          // The other health checks only operate on complete windows, and are processed later.
          // TODO: Confirm how repcnt is applied in bit-select mode
          update_repcnts(rng_val);
        end
      end

      `uvm_info(`gfn, "FULL_WINDOW", UVM_FULL)
      if (health_check_rng_data(window, ht_fips_mode, fw_ov_insert)) begin
        pass_cnt = 0;
      end else begin
        pass_cnt++;
      end

      window.delete();

      // Once in the halted state, or in the fw_ov_insert_entropy mode, pre-tested data is
      // discarded after the health checks
      if ((dut_fsm_phase == HALTED) || fw_ov_insert) begin
        continue;
      end

      `uvm_info(`gfn, $sformatf("pass_requirement: %01d", pass_requirement), UVM_HIGH)
      `uvm_info(`gfn, $sformatf("process_fifo_q.size: %01d", process_fifo_q.size()), UVM_HIGH)

      if (pass_cnt >= pass_requirement && !threshold_alert_active) begin
        package_and_release_entropy();
        // update counters for processing next seed:
        pass_cnt = 0;
        seed_idx++;
      end
    end : collect_entropy_loop
  endtask

  function void package_and_release_entropy();
    bit [FIPS_CSRNG_BUS_WIDTH - 1:0] fips_csrng;
    bit [CSRNG_BUS_WIDTH - 1:0] csrng_seed;
    bit entropy_data_reg_enable;

    entropy_data_reg_enable = (cfg.otp_en_es_fw_read == MuBi8True) &&
                              (ral.conf.entropy_data_reg_enable.get_mirrored_value() == MuBi4True);

    `uvm_info(`gfn, $sformatf("process_fifo_q.size(): %01d", process_fifo_q.size()), UVM_FULL)
    fips_csrng = predict_fips_csrng();

    // package data for routing to SW and to CSRNG:
    csrng_seed = get_csrng_seed(fips_csrng);

    // Only inject entropy data if entropy data is enabled
    if (entropy_data_reg_enable) begin
      entropy_data_q.push_back(csrng_seed);
    end

    fips_csrng_q.push_back(fips_csrng);

    // Check to see whether a recov_alert should be expected
    if (seed_idx != 0 && csrng_seed == prev_csrng_seed) begin
      set_exp_alert(.alert_name("recov_alert"), .is_fatal(0), .max_delay(cfg.alert_max_delay));
    end

    prev_csrng_seed = csrng_seed;

  endfunction

  virtual task process_csrng();
    push_pull_item#(.HostDataWidth(FIPS_CSRNG_BUS_WIDTH))  item;
    `uvm_info(`gfn, "task \"process_csrng\" starting\n", UVM_FULL)

    forever begin
      bit match_found = 0;

      csrng_fifo.get(item);
      if(!cfg.en_scb) begin
        continue;
      end
      `uvm_info(`gfn, $sformatf("process_csrng: new item: %096h\n", item.d_data), UVM_HIGH)

      while (fips_csrng_q.size() > 0) begin : seed_trial_loop
        bit [FIPS_CSRNG_BUS_WIDTH - 1:0] prediction;
        // Unlike in the TL case, there is no need to leave seed predictions in the queue.
        prediction = fips_csrng_q.pop_front();
        if (prediction == item.d_data) begin
          csrng_seeds++;
          match_found = 1;
          `uvm_info(`gfn, $sformatf("CSRNG Match found: %d\n", csrng_seeds), UVM_FULL)
          break;
        end else begin
          csrng_drops++;
          `uvm_info(`gfn, $sformatf("CSRNG Dropped seed: %d\n", csrng_drops), UVM_FULL)
          `uvm_info(`gfn, $sformatf("item: %0x\n", item.d_data), UVM_FULL)
          `uvm_info(`gfn, $sformatf("pred: %0x\n", prediction), UVM_FULL)
        end
      end : seed_trial_loop
      `DV_CHECK_EQ_FATAL(match_found, 1,
                         "All candidate csrng seeds have been checked, with no match")
    end
  endtask

  virtual function void process_observe_fifo_csr_access(tl_seq_item item, uvm_reg csr);
    bit [TL_DW - 1:0] csr_val;
    bit match_found = 0;
    string msg, fmt;
    bit fw_ov_enabled = (cfg.otp_en_es_fw_over == MuBi8True) &&
                        (ral.fw_ov_control.fw_ov_mode.get_mirrored_value() == MuBi4True);

    csr_val = item.d_data;

    fmt = "Predicting observe FIFO access, Looking for: %08x";
    msg = $sformatf(fmt, csr_val);
    `uvm_info(`gfn, msg, UVM_FULL)
    if (!fw_ov_enabled) begin
      // if fw_ov mode has never been enabled (and the programming model has been correctly
      // applied) then the observe fifo should be empty and cleared.
      msg = "Observe FIFO is disabled";
      `uvm_info(`gfn, msg, UVM_FULL)
      `DV_CHECK_FATAL(csr.predict(.value('0), .kind(UVM_PREDICT_READ)))
    end else begin
      msg = $sformatf("Checking %0d candidate seeds", observe_fifo_q.size());
      `uvm_info(`gfn, msg, UVM_FULL)
      while (observe_fifo_q.size() > 0) begin : seed_trial_loop
        bit [TL_DW - 1:0] prediction;
        // Unlike the ENTROPY_DATA CSR case, there is no need to leave seed predictions
        // in the queue.
        prediction = observe_fifo_q.pop_front();
        if (prediction == csr_val) begin
          `DV_CHECK_FATAL(csr.predict(.value(prediction), .kind(UVM_PREDICT_READ)))
          observe_fifo_words++;
          match_found = 1;
          cov_vif.cg_observe_fifo_sample(
              ral.conf.fips_enable.get_mirrored_value(),
              ral.conf.threshold_scope.get_mirrored_value(),
              ral.conf.rng_bit_enable.get_mirrored_value(),
              ral.conf.rng_bit_sel.get_mirrored_value(),
              ral.entropy_control.es_route.get_mirrored_value(),
              ral.entropy_control.es_type.get_mirrored_value(),
              ral.conf.entropy_data_reg_enable.get_mirrored_value(),
              cfg.otp_en_es_fw_read,
              ral.fw_ov_control.fw_ov_mode.get_mirrored_value(),
              ral.fw_ov_control.fw_ov_entropy_insert.get_mirrored_value()
          );
          msg = $sformatf("Match found: %d\n", observe_fifo_words);
          `uvm_info(`gfn, msg, UVM_FULL)
          break;
        end else begin
          observe_fifo_drops++;
          msg = $sformatf("Dropped word: %d\n", observe_fifo_drops);
          `uvm_info(`gfn, msg, UVM_FULL)
        end
      end : seed_trial_loop
      `DV_CHECK_EQ_FATAL(match_found, 1,
                        "All candidate observe FIFO words have been checked, with no match")
    end
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    if(kind == "HARD") begin
      // reset local fifos queues and variables
      handle_disable_reset(HardReset);
      // Immediately inform the collect_entropy process
      // that the IP is disabled
      dut_pipeline_enabled = 0;
    end
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass
