// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_scoreboard extends cip_base_scoreboard#(
    .CFG_T(entropy_src_env_cfg),
    .RAL_T(entropy_src_reg_block),
    .COV_T(entropy_src_env_cov)
  );

  `uvm_component_utils(entropy_src_scoreboard)

  // TODO (Cleanup): Put the DUT-internal constant (`PreCondWidth`) into a package and use it here.
  localparam int SHACondWidth     = 64;
  localparam int ObserveFifoDepth = entropy_src_reg_pkg::ObserveFifoDepth;

  intr_vif                                     interrupt_vif;
  virtual entropy_src_cov_if                   cov_vif;

  // used by health_test_scoring_thread to predict the FSMs phase
  // when constructing seeds
  int seed_idx             = 0;
  // number of seeds output since enable (or reset)
  int seeds_out            = 0;

  int entropy_data_seeds    = 0;
  int entropy_data_drops    = 0;
  int csrng_seeds           = 0;
  int csrng_drops           = 0;
  int observe_fifo_words    = 0;
  int observe_fifo_drops    = 0;
  bit observe_fifo_overflow = 0;
  int overflow_read_cnt     = 0;

  bit dut_pipeline_enabled = 0;
  bit regwen_pending = 0;
  bit ht_fips_mode = 0;

  // The FW_OV pipeline is controlled by two variables: SHA3_START and MODULE_ENABLE
  // The MODULE_ENABLE signal has different delays when shutting down the FW_OV pipeline
  // so we track it in a separate variable for fw_ov
  bit fw_ov_sha_enabled    = 0;
  bit fw_ov_pipe_enabled   = 0;

  // This scoreboard is not capable of anticipating with single-cycle accuracy whether the observe
  // and entropy data FIFOs are empty.  However, we can note when they have been explicitly cleared
  // and use that to anticipate any alerts that may come about background diable events
  bit fifos_cleared = 1;

  // Queue of RNG data for health testing
  queue_of_rng_val_t               health_test_data_q;

  // Queue of seeds for predicting reads to entropy_data CSR
  bit [CSRNG_BUS_WIDTH - 1:0]      entropy_data_q[$];

  // Queue of TL_DW words for predicting outputs of the observe FIFO
  bit [TL_DW - 1:0]                observe_fifo_q[$];
  bit                              overflow_condition = 0;
  bit                              observe_read_incoming = 0;
  bit [TL_DW - 1:0]                fw_ov_wr_fifo_full_prediction = '0;
  bit                              precon_fifo_full = 0;
  bit                              precon_fifo_full_q = 0;

  // Queue of 64-bit words for inserting entropy input to the SHA (or raw) pipelines
  bit [SHACondWidth - 1:0]         sha_process_q[$];
  bit [TL_DW - 1:0]                raw_process_q[$];

  // Buffer to store SHA entropy when using FW_OV mode
  bit [SHACondWidth - 1:0]         repacked_entropy_fw_ov;
  int                              repack_idx_fw_ov = 0;

  // The most recent candidate seed from entropy_data_q
  // At each TL read the TL data item is compared to the appropriate
  // 32-bit segment of this seed (as determented by seed_tl_read_cnt)
  bit [CSRNG_BUS_WIDTH - 1:0]      tl_best_seed_candidate;

  // The previous output seed (+ fips bit)  We need to track this to determine whether to expect
  // the bus_cmp recov_alert
  bit [CSRNG_BUS_WIDTH : 0]        prev_csrng_seed;

  // Number of 32-bit TL reads to the current (active) seed
  // Ranges from 0 (no data read out) to CSRNG_BUS_WIDTH/TL_DW (seed fully read out)
  int                              seed_tl_read_cnt = 0;

  bit [FIPS_CSRNG_BUS_WIDTH - 1:0] fips_csrng_q[$];

  // TODO: Document Initial Conditions for health check.
  // This should make no practical difference, but it is important for successful verification.
  rng_val_t                        prev_rng_val = '0;
  int                              repcnt      [RNG_BUS_WIDTH];
  int                              repcnt_symbol;

  // Total number of repcnt OR repcnts failures for a particular sample.
  // Some care is required in counting total failures as different
  // types of failures happening in the same sample only get counted once.
  int                              continuous_fail_count;
  bit                              cont_fail_in_last_sample;

  // Predicted value of internal repetition counters.
  bit [15:0] repcnt_event_cnt;
  bit [15:0] repcnts_event_cnt;

  // Ext. HT counters.
  // Like the continuous tests, these failures can in principle happen many times
  // per window, however only one failure per window gets registered toward the
  // total alert count.
  int                              extht_fail_count;
  int                              extht_fail_in_last_sample;

  bit threshold_alert_active = 1'b0;

  // Signal to indicate that the main sm is going into the error state
  bit main_sm_escalates = 0;

  // Bit to signify that the module_enable bit is locked
  bit dut_me_reglocked = 1'b0;

  // TLM agent fifos
  uvm_tlm_analysis_fifo#(push_pull_item#(.HostDataWidth(FIPS_CSRNG_BUS_WIDTH)))
      csrng_fifo;
  uvm_tlm_analysis_fifo#(push_pull_item#(.HostDataWidth(RNG_BUS_WIDTH)))
      rng_fifo;
  uvm_tlm_analysis_fifo#(entropy_src_xht_item) xht_fifo;

  // Interrupt Management Variables

  // To track interrupt events we need to identify interupts have
  // been previously observed to be high.
  //
  // An interrupt that was previously high is ignored until
  // it is observed to be high again.
  //
  // Interrupts go high when a new interrupt is observed
  // Interrupts should go low when an interrupt is cleared
  bit [NumEntropySrcIntr - 1:0] known_intr_state = '0;

  bit [NumEntropySrcIntr - 1:0] intr_en_mask = '0;
  bit [NumEntropySrcIntr - 1:0] intr_test = '0;
  bit                           intr_test_active = '0;

  // Indicates that the observe fifo should have data in it.
  // Switches to OBSERVE_FIFO_THRESHOLD when:
  //   A. A new observe fifo interrupt has been received.
  //   B. The interrupt has been cleared, but it persists a cycle later.
  // Decrements by one when the fifo is read.
  // Is cleared on Reset, or Disable, (stays cleared until enable)
  int expected_obsfifo_entries_since_last_intr  = 0;

  // Signal to communicate that TL data has inserted into the FW_OV FIFO at an invalid time.
  // The DUT ignores such inputs and raises an alert.  However in the interest of testing the
  // response to the DUT to all the _ data that comes in, we mimic the DUT and ignore
  // these data points once we notice one of these events.
  bit ignore_fw_ov_data_pulse = 0;

  // Variables used to predict the observe FIFO depth.
  bit observe_push_busy_addr_phase = 0;
  bit observe_push_busy = 0;

  // Variables used to predict whether the precon FIFO is full or not.
  int precon_fifo_cnt = 0;
  bit sha3_msg_ready = 0;
  bit predict_fw_ov_wr_fifo_full = 0;
  string pad_st_path = "tb.dut.u_entropy_src_core.u_sha3.u_pad.st[6:0]";
  string pad_st_d_path = "tb.dut.u_entropy_src_core.u_sha3.u_pad.st_d[6:0]";
  string aes_halt_o_path = "tb.dut.cs_aes_halt_o";

  // Variables used to model entropy propagating through the pipeline.
  int                       post_ht_drops = 0;
  bit                       fw_ov_insert;
  bit                       esbit_fifo_processed = 1;
  bit                       esbit_last_full_cycle = 0;
  bit                       postht_fifo_processed = 1;
  bit                       postht_last_full_cycle = 0;
  bit                       distr_fifo_processed = 1;
  bit                       observe_fifo_processed = 1;
  bit                       bypass_fifo_processed = 1;
  bit                       precon_fifo_processed = 1;
  bit                       sha3_ready_predicted = 1;
  bit                       fw_ov_sha3_started = 0;
  bit [3:0]                 esrng_fifo_q[$];
  bit [3:0]                 esbit_fifo_q[$];
  bit [TL_DW - 1:0]         postht_fifo_q[$];
  bit [TL_DW - 1:0]         distr_fifo_q[$];
  bit [TL_DW - 1:0]         distr_to_observe_fifo_q[$];
  bit [TL_DW - 1:0]         distr_to_bypass_fifo_q[$];
  bit [TL_DW - 1:0]         distr_to_precon_fifo_q[$];

  // This enum type contains the states used for the FSM in sha3pad.sv.
  localparam int StateWidthPad = 7;
  typedef enum logic [StateWidthPad-1:0] {
    StPadIdle = 7'b1000010,
    StPrefix = 7'b0111100,
    StPrefixWait =7'b1001100,
    StMessage = 7'b0100101,
    StMessageWait = 7'b0001111,
    StPad = 7'b1111010,
    StPadRun = 7'b0011001,
    StPad01 = 7'b1101001,
    StPadFlush = 7'b1010111,
    StTerminalError = 7'b0110011
  } pad_st_e;

  // Enabling, disabling and reset all have some effect in clearing the state of the DUT
  // Due to subleties in timing, the DUT resets the Observe FIFO with a unique delay
  typedef enum int {
    HardReset,
    Disable,
    Enable,
    FIFOClr,
    FWOVDisable
  } reset_event_e;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    rng_fifo   = new("rng_fifo", this);
    csrng_fifo = new("csrng_fifo", this);
    xht_fifo   = new("xht_fifo", this);

    if (!uvm_config_db#(virtual entropy_src_cov_if)::get
       (null, "*.env" , "entropy_src_cov_if", cov_vif)) begin
       `uvm_fatal(`gfn, $sformatf("Failed to get entropy_src_cov_if from uvm_config_db"))
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    // When seeing unexpected alerts during debugging, disable the alert checking.
    //do_alert_check = 0;
    super.run_phase(phase);
    if (cfg.en_scb) begin
      fork
        process_csrng();
        process_interrupts();
        process_fifo_exceptions();
        health_test_scoring_thread();
        process_xht();
        predict_fw_ov_wr_full();
        process_esrng_fifo();
        process_esbit_fifo();
        process_postht_fifo();
        process_distr_fifo();
        process_observe_fifo();
        process_bypass_fifo();
        process_precon_fifo();
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

  function void update_repcnts(bit fips_mode, rng_val_t rng_val);
    int           max_repcnt = 0;
    bit           repcnt_fail, repcnt_sym_fail;
    uvm_reg_field alert_summary_field = ral.alert_summary_fail_counts.any_fail_count;
    int           any_fail_count_regval;
    string        fmt;
    bit           rng_bit_en = (`gmv(ral.conf.rng_bit_enable) == MuBi4True);
    int           rng_bit_sel = `gmv(ral.conf.rng_bit_sel);

    for (int i = 0; i < RNG_BUS_WIDTH; i++) begin
      if (rng_val[i] == prev_rng_val[i]) begin
        repcnt[i]++;
      end else begin
        repcnt[i] = 1;
      end
      max_repcnt = (repcnt[i] > max_repcnt) ? repcnt[i] : max_repcnt;
    end
    // Overwrite max_repcnt with the value of the selected lane if the single lane mode is active.
    if (rng_bit_en) begin
      max_repcnt = repcnt[rng_bit_sel];
    end
    `uvm_info(`gfn, $sformatf("max repcnt %0h", max_repcnt), UVM_DEBUG)
    repcnt_fail = evaluate_repcnt_test(fips_mode, max_repcnt);

    if (rng_val == prev_rng_val) begin
      repcnt_symbol++;
    end else begin
      repcnt_symbol = 1;
    end
    repcnt_sym_fail = evaluate_repcnt_symbol_test(fips_mode, repcnt_symbol);

    cont_fail_in_last_sample = repcnt_fail | repcnt_sym_fail;
    continuous_fail_count += cont_fail_in_last_sample;

    any_fail_count_regval = `gmv(alert_summary_field);
    any_fail_count_regval += cont_fail_in_last_sample;
    `DV_CHECK_FATAL(alert_summary_field.predict(.value(any_fail_count_regval),
                                                .kind(UVM_PREDICT_DIRECT)))

    if(cont_fail_in_last_sample) begin
      fmt = "Predicted alert cnt for all tests: %04h";
      `uvm_info(`gfn, $sformatf(fmt, any_fail_count_regval), UVM_HIGH)
    end

    prev_rng_val = rng_val;
  endfunction

  function int calc_adaptp_test(queue_of_rng_val_t window, output int maxval, output int minval);
    int test_cnt[RNG_BUS_WIDTH];
    int minq[$], maxq[$];
    int result = '0;
    bit rng_bit_en = (`gmv(ral.conf.rng_bit_enable) == MuBi4True);
    int rng_bit_sel = `gmv(ral.conf.rng_bit_sel);
    for (int i = 0; i < window.size(); i++) begin
      for (int j = 0; j < RNG_BUS_WIDTH; j++) begin
         test_cnt[j] += window[i][j];
      end
    end
    // If the single lane mode is active set the min the max and the return value
    // to the test_cnt of the selected lane.
    if (rng_bit_en) begin
      maxval = test_cnt[rng_bit_sel];
      minval = test_cnt[rng_bit_sel];
      return test_cnt[rng_bit_sel];
    end else begin
      maxq = test_cnt.max();
      maxval = maxq[0];
      minq = test_cnt.min();
      minval = minq[0];
      return test_cnt.sum();
    end
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
    bit rng_bit_en = (`gmv(ral.conf.rng_bit_enable) == MuBi4True);
    int rng_bit_sel = `gmv(ral.conf.rng_bit_sel);
    // Round down to the highest even number.
    // The window size can be odd when entropy drops happened.
    int window_size = (window.size() % 2) ? window.size() - 1 : window.size();
    for (int i = 0; i < window_size; i += 2) begin
      for (int j = 0; j < RNG_BUS_WIDTH; j++) begin
        bit different = window[i][j] ^ window[i + 1][j];
        pair_cnt[j] += different;
      end
    end
    // If the single lane mode is active set the min the max and the return value
    // to the pair_cnt of the selected lane.
    if (rng_bit_en) begin
      maxval = pair_cnt[rng_bit_sel];
      minval = pair_cnt[rng_bit_sel];
      return pair_cnt[rng_bit_sel];
    end else begin
      maxq = pair_cnt.max();
      maxval = maxq[0];
      minq = pair_cnt.min();
      minval = minq[0];
      return pair_cnt.sum();
    end
  endfunction

  function int calc_extht_test(queue_of_rng_val_t window);
    // TODO(#16276)
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
      // Update predicted value of internal repetition counter even if the watermark does not
      // increase.
      if (test == "repcnt_hi") begin
        repcnt_event_cnt = value;
      end else if (test == "repcnts_hi") begin
        repcnts_event_cnt = value;
      end
      // Update predicted watermark value if appropriate.
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
  // Because failing multiple tests for a single test only count as one total alert failure
  // this routine does not update alert_summary_fail_counts
  //

  function void predict_failure_logs(string test);
    string        total_fail_reg_name;
    string        total_fail_field_name;
    string        alert_cnt_reg_name;
    string        alert_cnt_field_name;
    uvm_reg       total_fail_reg;
    uvm_reg       alert_cnt_reg;
    uvm_reg_field total_fail_field;
    uvm_reg_field alert_cnt_field;

    bit [3:0]     alert_cnt;
    int           fail_total;

    string        fmt, msg;

    validate_test_name(test);
    total_fail_reg_name = $sformatf("%s_total_fails", test);
    total_fail_field_name = total_fail_reg_name;

    // Most tests have field in the alert_fail_counts register, except extht_fail_counts
    if (test.substr(0, 5) == "extht_") begin
      alert_cnt_reg_name = "extht_fail_counts";
    end else begin
      alert_cnt_reg_name = "alert_fail_counts";
    end
    alert_cnt_field_name = $sformatf("%s_fail_count", test);

    total_fail_reg   = ral.get_reg_by_name(total_fail_reg_name);
    total_fail_field = total_fail_reg.get_field_by_name(total_fail_field_name);

    alert_cnt_reg    = ral.get_reg_by_name(alert_cnt_reg_name);
    alert_cnt_field  = alert_cnt_reg.get_field_by_name(alert_cnt_field_name);

    fail_total = total_fail_field.get_mirrored_value();
    alert_cnt  =  alert_cnt_field.get_mirrored_value();

    // Update the predicted failure counters, noting that the DUT will not let these overflow
    alert_cnt  += (&alert_cnt)  ? 0 : 1;
    fail_total += (&fail_total) ? 0 : 1;

    fmt = "Previous alert cnt reg: %08h";
    msg = $sformatf(fmt, alert_cnt_reg.get_mirrored_value());
    `uvm_info(`gfn, msg, UVM_DEBUG)

    `DV_CHECK_FATAL(total_fail_field.predict(.value(fail_total), .kind(UVM_PREDICT_DIRECT)))
    `DV_CHECK_FATAL( alert_cnt_field.predict(.value( alert_cnt), .kind(UVM_PREDICT_DIRECT)))

    fmt = "Predicted alert cnt for \"%s\" test: %04h";
    msg = $sformatf(fmt, test, alert_cnt_field.get_mirrored_value());
    `uvm_info(`gfn, msg, UVM_HIGH)

    fmt = "Entire alert cnt reg: %08h";
    msg = $sformatf(fmt, alert_cnt_reg.get_mirrored_value());
    `uvm_info(`gfn, msg, UVM_FULL)

    fmt = "Predicted fail cnt for \"%s\" test: %01h";
    msg = $sformatf(fmt, test, total_fail_field.get_mirrored_value());
    `uvm_info(`gfn, msg, UVM_HIGH)
  endfunction

  function bit check_threshold(string test, bit fips_mode, int value);
    string        threshold_reg_name;
    string        threshold_field_name;
    uvm_reg       threshold_reg;
    uvm_reg_field threshold_field;

    int        threshold_val;
    bit        continuous_test;
    bit        failure;
    bit        low_test;
    string     fmt, msg;

    validate_test_name(test);
    low_test             = is_low_test(test);
    continuous_test      = (test == "repcnt") || (test == "repcnts");

    threshold_field_name = fips_mode ? "fips_thresh" : "bypass_thresh";
    threshold_reg_name  = $sformatf("%s_thresholds", test);

    threshold_reg    = ral.get_reg_by_name(threshold_reg_name);
    threshold_field  = threshold_reg.get_field_by_name(threshold_field_name);

    threshold_val = threshold_field.get_mirrored_value();

    // Continuous tests are more rigorous about holding to the '>=' specified in NIST
    // 800-90B. Meanwhile the windowed tests use "<" or ">" as this allows these tests
    // to be temporarily disabled at boot, by choosing the maximal window size.
    // TODO: Document this
    if (continuous_test) begin
      failure = (low_test && value <= threshold_val) || (!low_test && value >= threshold_val);
    end else begin
      failure = (low_test && value < threshold_val) || (!low_test && value > threshold_val);
    end

    fmt = "Threshold for \"%s\" test (FIPS? %d): %04h";
    `uvm_info(`gfn, $sformatf(fmt, test, fips_mode, threshold_val), UVM_FULL)

    fmt = "Observed value for \"%s\" test (FIPS? %d): %04h, %s";
    `uvm_info(`gfn, $sformatf(fmt, test, fips_mode, value, failure ? "FAIL" : "PASS"), UVM_FULL)

    return failure;

  endfunction


  // Indicates that the health test is active
  // Also indicates whether the sigma value in the dut_cfg is being employed
  function bit ht_is_active();
    bit fw_insert, sigma_applied;

    fw_insert = (ral.fw_ov_control.fw_ov_mode.get_mirrored_value() == MuBi4True) &&
                (ral.fw_ov_control.fw_ov_entropy_insert.get_mirrored_value() == MuBi4True);

    // TODO (Priority 3): This use of the dut_cfg depends very much on the vseq being employed.
    sigma_applied = !cfg.dut_cfg.default_ht_thresholds;

    return !fw_insert && sigma_applied;

  endfunction

  function bit evaluate_adaptp_test(queue_of_rng_val_t window, bit fips_mode);
    int value, minval, maxval;
    bit fail_hi, fail_lo;
    bit total_scope;
    int threshold_hi, threshold_lo;
    real sigma_hi, sigma_lo;

    int window_size = fips_mode ? `gmv(ral.health_test_windows.fips_window) :
                                  `gmv(ral.health_test_windows.bypass_window);

    // If rng_bit_enable is set to MuBi4True, the window size is 4 times as large.
    // We need the same number of bits but only have a single lane.
    int window_size_scaled = (`gmv(ral.conf.rng_bit_enable) == MuBi4True) ? 4*window_size :
                                                                            window_size;

    threshold_hi = fips_mode ? `gmv(ral.adaptp_hi_thresholds.fips_thresh) :
                               `gmv(ral.adaptp_hi_thresholds.bypass_thresh);

    threshold_lo = fips_mode ? `gmv(ral.adaptp_lo_thresholds.fips_thresh) :
                               `gmv(ral.adaptp_lo_thresholds.bypass_thresh);

    total_scope = (ral.conf.threshold_scope.get_mirrored_value() == MuBi4True);

    sigma_hi = ideal_threshold_to_sigma(window_size_scaled, adaptp_ht, !total_scope,
                                        high_test, threshold_hi);
    sigma_lo = ideal_threshold_to_sigma(window_size_scaled, adaptp_ht, !total_scope,
                                        low_test, threshold_lo);

    value = calc_adaptp_test(window, maxval, minval);

    update_watermark("adaptp_lo", fips_mode, total_scope ? value : minval);
    update_watermark("adaptp_hi", fips_mode, total_scope ? value : maxval);

    fail_lo = check_threshold("adaptp_lo", fips_mode, total_scope ? value : minval);
    if (fail_lo) predict_failure_logs("adaptp_lo");

    fail_hi = check_threshold("adaptp_hi", fips_mode, total_scope ? value : maxval);
    if (fail_hi) predict_failure_logs("adaptp_hi");


    if (ht_is_active()) begin
      cov_vif.cg_win_ht_sample(adaptp_ht, high_test, window_size_scaled * RNG_BUS_WIDTH, fail_hi);
      cov_vif.cg_win_ht_sample(adaptp_ht, low_test, window_size_scaled * RNG_BUS_WIDTH, fail_lo);
      cov_vif.cg_win_ht_deep_threshold_sample(adaptp_ht, high_test,
                                              window_size_scaled * RNG_BUS_WIDTH,
                                              !total_scope, sigma_hi, fail_hi);
      cov_vif.cg_win_ht_deep_threshold_sample(adaptp_ht, low_test,
                                              window_size_scaled * RNG_BUS_WIDTH,
                                              !total_scope, sigma_lo, fail_lo);
    end

    return (fail_hi || fail_lo);
  endfunction

  function bit evaluate_bucket_test(queue_of_rng_val_t window, bit fips_mode);
    int value;
    bit fail;
    int threshold;
    real sigma;

    int window_size = fips_mode ? `gmv(ral.health_test_windows.fips_window) :
                                  `gmv(ral.health_test_windows.bypass_window);

    // If rng_bit_enable is set to MuBi4True, the window size is 4 times as large.
    // We need the same number of bits but only have a single lane.
    int window_size_scaled = (`gmv(ral.conf.rng_bit_enable) == MuBi4True) ? 4*window_size :
                                                                            window_size;

    threshold = fips_mode ? `gmv(ral.bucket_thresholds.fips_thresh) :
                            `gmv(ral.bucket_thresholds.bypass_thresh);

    sigma = ideal_threshold_to_sigma(window_size_scaled, bucket_ht, 0, high_test, threshold);

    value = calc_bucket_test(window);

    update_watermark("bucket", fips_mode, value);

    fail = check_threshold("bucket", fips_mode, value);
    if (fail) predict_failure_logs("bucket");

    if (ht_is_active()) begin
      cov_vif.cg_win_ht_sample(bucket_ht, high_test, window_size_scaled*RNG_BUS_WIDTH, fail);
      cov_vif.cg_win_ht_deep_threshold_sample(bucket_ht, high_test,
                                              window_size_scaled*RNG_BUS_WIDTH,
                                              1'b0, sigma, fail);
    end

    return fail;
  endfunction

  function bit evaluate_markov_test(queue_of_rng_val_t window, bit fips_mode);
    int value, minval, maxval;
    bit fail_hi, fail_lo;
    bit total_scope;
    int threshold_hi, threshold_lo;
    real sigma_hi, sigma_lo;

    int window_size = fips_mode ? `gmv(ral.health_test_windows.fips_window) :
                                  `gmv(ral.health_test_windows.bypass_window);

    // If rng_bit_enable is set to MuBi4True, the window size is 4 times as large.
    // We need the same number of bits but only have a single lane.
    int window_size_scaled = (`gmv(ral.conf.rng_bit_enable) == MuBi4True) ? 4*window_size :
                                                                            window_size;

    threshold_hi = fips_mode ? `gmv(ral.markov_hi_thresholds.fips_thresh) :
                               `gmv(ral.markov_hi_thresholds.bypass_thresh);

    threshold_lo = fips_mode ? `gmv(ral.markov_lo_thresholds.fips_thresh) :
                               `gmv(ral.markov_lo_thresholds.bypass_thresh);

    total_scope = (ral.conf.threshold_scope.get_mirrored_value() == MuBi4True);

    sigma_hi = ideal_threshold_to_sigma(window_size_scaled, markov_ht, !total_scope,
                                        high_test, threshold_hi);
    sigma_lo = ideal_threshold_to_sigma(window_size_scaled, markov_ht, !total_scope,
                                        low_test, threshold_lo);

    value = calc_markov_test(window, maxval, minval);

    update_watermark("markov_lo", fips_mode, total_scope ? value : minval);
    update_watermark("markov_hi", fips_mode, total_scope ? value : maxval);

    fail_lo = check_threshold("markov_lo", fips_mode, total_scope ? value : minval);
    if (fail_lo) predict_failure_logs("markov_lo");

    fail_hi = check_threshold("markov_hi", fips_mode, total_scope ? value : maxval);
    if (fail_hi) predict_failure_logs("markov_hi");

    if (ht_is_active()) begin
      cov_vif.cg_win_ht_sample(markov_ht, high_test, window_size_scaled*RNG_BUS_WIDTH, fail_hi);
      cov_vif.cg_win_ht_sample(markov_ht, low_test, window_size_scaled*RNG_BUS_WIDTH, fail_lo);
      cov_vif.cg_win_ht_deep_threshold_sample(markov_ht, high_test,
                                              window_size_scaled*RNG_BUS_WIDTH,
                                              !total_scope, sigma_hi, fail_hi);
      cov_vif.cg_win_ht_deep_threshold_sample(markov_ht, low_test,
                                              window_size_scaled*RNG_BUS_WIDTH,
                                              !total_scope, sigma_hi, fail_lo);
    end

    return (fail_hi || fail_lo);
  endfunction

  function void evaluate_external_ht(entropy_src_xht_rsp_t xht_rsp, bit fips_mode);
    int value_hi, value_lo;
    bit fail_hi, fail_lo;
    string msg;

    value_hi = xht_rsp.test_cnt_hi;
    value_lo = xht_rsp.test_cnt_lo;

    fail_hi = xht_rsp.test_fail_hi_pulse;
    fail_lo = xht_rsp.test_fail_lo_pulse;

    update_watermark("extht_lo", fips_mode, value_lo);
    update_watermark("extht_hi", fips_mode, value_hi);

    if (fail_lo) predict_failure_logs("extht_lo");

    if (fail_hi) predict_failure_logs("extht_hi");

    extht_fail_count += (fail_hi || fail_lo);
    extht_fail_in_last_sample = fail_hi || fail_lo;
  endfunction

  // The repetition counts are always running
  function bit evaluate_repcnt_test(bit fips_mode, int value);
    bit fail;
    bit rng_en = (`gmv(ral.conf.rng_bit_enable) == MuBi4True);

    update_watermark("repcnt", fips_mode, value);

    fail = check_threshold("repcnt", fips_mode, value);
    if (fail) begin
      `uvm_info(`gfn, "repcnt failure detected", UVM_FULL)
      predict_failure_logs("repcnt");
    end

    if (ht_is_active()) begin
      cov_vif.cg_cont_ht_sample(repcnt_ht, fips_mode, rng_en, `gmv(ral.conf.rng_bit_sel),
                                value, fail);
    end

    return fail;

  endfunction

  function bit evaluate_repcnt_symbol_test(bit fips_mode, int value);
    bit fail;
    bit rng_en = (`gmv(ral.conf.rng_bit_enable) == MuBi4True);

    update_watermark("repcnts", fips_mode, value);

    fail = check_threshold("repcnts", fips_mode, value);
    if (fail) begin
      `uvm_info(`gfn, "repcnts failure detected", UVM_FULL)
      predict_failure_logs("repcnts");
    end

    if (ht_is_active()) begin
      cov_vif.cg_cont_ht_sample(repcnts_ht, fips_mode, rng_en, `gmv(ral.conf.rng_bit_sel),
                                value, fail);
    end

    return fail;
  endfunction

  function int health_check_rng_data(queue_of_rng_val_t window,
                                     bit fips_mode);
    int           windowed_fail_count;
    int           total_fail_count;
    int           overcount;
    bit           sample_fail_count;
    uvm_reg_field alert_summary_field = ral.alert_summary_fail_counts.any_fail_count;
    int           any_fail_count_regval;
    string        fmt;

    windowed_fail_count = evaluate_adaptp_test(window, fips_mode) +
                          evaluate_bucket_test(window, fips_mode) +
                          evaluate_markov_test(window, fips_mode);

    // Are there any failures this in the last sample (continuous or windowed)?
    // Note: If the last sample in the window has a continuous HT failure, then
    // this sample has already been added to the failure counts
    sample_fail_count = (windowed_fail_count != 0);

    // Add the number of continuous fails (excluding the last sample)
    // to any failure in this sample.
    total_fail_count = sample_fail_count + continuous_fail_count + extht_fail_count;

    // Implementation artifact:
    // Account for the fact that simultaneous failures for windowed, continuous and ExtHT tests
    // only get counted once in the total failure count if they coincidentally occur in the last
    // sample.
    overcount = sample_fail_count + cont_fail_in_last_sample + extht_fail_in_last_sample;
    overcount -= (overcount >= 1);
    total_fail_count -= overcount;

    // To avoid double counting only mark a sample failure if there haven't
    // already been continuous or extht failures at the same time.
    if (sample_fail_count && !(cont_fail_in_last_sample || extht_fail_in_last_sample)) begin
      any_fail_count_regval = `gmv(alert_summary_field);
      // Just add any failure in the last sample as the previous samples
      // were added as they occurred.
      any_fail_count_regval++;
      `DV_CHECK_FATAL(alert_summary_field.predict(.value(any_fail_count_regval),
                                                  .kind(UVM_PREDICT_DIRECT)))
      fmt = "Predicted alert cnt for all tests: %04h";
      `uvm_info(`gfn, $sformatf(fmt, any_fail_count_regval), UVM_HIGH)
    end

    continuous_fail_count = 0;
    extht_fail_count = 0;

    return total_fail_count;
  endfunction

  function void process_failures(int total_fail_count,
                                 bit fw_ov_insert,
                                 entropy_phase_e dut_phase,
                                 int successive_win_fail_count);

    bit failure             = 0;

    uvm_reg       alert_fail_reg      = ral.alert_fail_counts;
    uvm_reg       extht_fail_reg      = ral.extht_fail_counts;
    uvm_reg_field any_fail_count_fld  = ral.alert_summary_fail_counts.any_fail_count;
    string        fmt;
    int           any_fail_count_regval;
    int           alert_threshold;
    bit           main_sm_exp_alert_cond;

    // TODO (#18889): If an alert is anticipated, we should check that (if necessary) this seed is
    // stopped and no others are allowed to progress.
    alert_threshold = `gmv(ral.alert_threshold.alert_threshold);

    fmt = "Predicting alert status with %0d new failures this window";
    `uvm_info(`gfn, $sformatf(fmt, total_fail_count), UVM_FULL)

    any_fail_count_regval = `gmv(any_fail_count_fld);

    failure = (total_fail_count != 0);
    main_sm_exp_alert_cond = (dut_phase == STARTUP) ?
                             (successive_win_fail_count >= 2) :
                             (any_fail_count_regval >= alert_threshold);

    if (failure) begin : test_failure
      if (main_sm_exp_alert_cond) begin
        if (!fw_ov_insert && !threshold_alert_active && !main_sm_escalates) begin
          if (dut_phase == STARTUP) begin
            fmt =  "New alert anticpated with >= 2 failing windows." +
                   "(supercedes count/threshold of %01d/%01d)";
          end else begin
            fmt = "New alert anticpated! Fail count (%01d) >= threshold (%01d)";
          end
          threshold_alert_active = 1;
          `DV_CHECK_FATAL(ral.recov_alert_sts.es_main_sm_alert.predict(1'b1));
          set_exp_alert(.alert_name("recov_alert"), .is_fatal(0), .max_delay(cfg.alert_max_delay));
          // The DUT should either set the alert, or crash the sim.
          // If we succeed, sample this alert_threshold as covered successfully.
          cov_vif.cg_alert_cnt_sample(alert_threshold, 1);
        end else if (main_sm_escalates) begin
          fmt = "Main SM in error state, overrides recov alert (Fail cnt: %01d,  thresh: %01d)";
        end else if(threshold_alert_active) begin
          fmt = "Alert already signalled:  Fail count (%01d) >= threshold (%01d)";
        end else begin
          fmt = "FW_OV mode, alerts suppressed:  Fail count (%01d) >= threshold (%01d)";
        end
        `uvm_info(`gfn, $sformatf(fmt, any_fail_count_regval, alert_threshold), UVM_HIGH)
      end else begin
        fmt = "No alert anticpated. fail count (%01d) < threshold (%01d)";
        `uvm_info(`gfn, $sformatf(fmt, any_fail_count_regval, alert_threshold), UVM_HIGH)
      end
    end else begin : no_test_failure
      if (!fw_ov_insert && !threshold_alert_active && !main_sm_escalates) begin
        // Now we know that all tests have passed we can clear the failure counts. In FW_OV mode
        // alerts are suppressed but we keep counting failures. In addition, even in case of a
        // full passing test sequence, counters are not cleared.
        `DV_CHECK_FATAL(alert_fail_reg.predict(.value({TL_DW{1'b0}}), .kind(UVM_PREDICT_DIRECT)))
        `DV_CHECK_FATAL(extht_fail_reg.predict(.value({TL_DW{1'b0}}), .kind(UVM_PREDICT_DIRECT)))
        `DV_CHECK_FATAL(any_fail_count_fld.predict(.value('0), .kind(UVM_PREDICT_DIRECT)))
      end else begin
        fmt = "Alert state persists: Fail count (%01d) >= threshold (%01d)";
        `uvm_info(`gfn, $sformatf(fmt, any_fail_count_regval, alert_threshold), UVM_HIGH)
      end
    end : no_test_failure

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
            bit [CSRNG_BUS_WIDTH - 1:0] full_seed;

            full_seed_found = 1;
            seed_tl_read_cnt = 0;
            full_seed = entropy_data_q.pop_front();
            entropy_data_seeds++;
            cfg.total_seeds_consumed++;

          end else if (seed_tl_read_cnt > CSRNG_BUS_WIDTH / TL_DW) begin
            `uvm_error(`gfn, "testbench error: too many segments read from candidate seed")
          end
          cov_vif.cg_seed_output_csr_sample(
              mubi4_t'(ral.conf.fips_enable.get_mirrored_value()),
              mubi4_t'(ral.conf.fips_flag.get_mirrored_value()),
              mubi4_t'(ral.conf.rng_fips.get_mirrored_value()),
              mubi4_t'(ral.conf.threshold_scope.get_mirrored_value()),
              mubi4_t'(ral.conf.rng_bit_enable.get_mirrored_value()),
              ral.conf.rng_bit_sel.get_mirrored_value(),
              mubi4_t'(ral.entropy_control.es_route.get_mirrored_value()),
              mubi4_t'(ral.entropy_control.es_type.get_mirrored_value()),
              mubi4_t'(ral.conf.entropy_data_reg_enable.get_mirrored_value()),
              mubi8_t'(cfg.otp_en_es_fw_read),
              mubi4_t'(ral.fw_ov_control.fw_ov_mode.get_mirrored_value()),
              mubi8_t'(cfg.otp_en_es_fw_over),
              mubi4_t'(ral.fw_ov_control.fw_ov_entropy_insert.get_mirrored_value()),
              full_seed_found
          );
          break;
        end else begin
          void'(entropy_data_q.pop_front());
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
    bit is_fw_ov = (`gmv(ral.fw_ov_control.fw_ov_mode) == MuBi4True) &&
                   (`gmv(ral.fw_ov_control.fw_ov_entropy_insert) == MuBi4True);

    if (rst_type == Enable) begin
      // Stop ignoring alerts as soon as ENTROPY_SRC is turned on.
      ignore_exp_alert = 0;
      clear_ht_stat_predictions();
      seeds_out = 0;
      health_test_data_q.delete();
      // Wait until the precon FIFO is not full anymore and update precon_fifo_full
      // and precon_fifo_cnt for the prediction of fw_ov_wr_fifo_full.
      fork
        begin
          bit [StateWidthPad-1:0] sha3pad_state, sha3pad_state_next;
          bit cs_aes_halt_o;
          // Wait one cycle for the precon FIFO clear signal to go low.
          cfg.clk_rst_vif.wait_clks(1);
          do begin
            // Wait one cycle for the FIFO not full signal to potentially go high.
            cfg.clk_rst_vif.wait_clks(1);
            `DV_CHECK(uvm_hdl_read(pad_st_path, sha3pad_state))
            `DV_CHECK(uvm_hdl_read(pad_st_d_path, sha3pad_state_next))
            `DV_CHECK(uvm_hdl_read(aes_halt_o_path, cs_aes_halt_o))
            sha3_msg_ready = !cs_aes_halt_o && (sha3pad_state == StMessage) &&
                             (sha3pad_state_next == StMessage);
          end while (!sha3_msg_ready);
          precon_fifo_full = 0;
          precon_fifo_cnt = 0;
        end
      join_none
    end

    // Internal CSRNG stores and scoreboard state is cleared on Disable and HardReset events.
    if( rst_type == Disable || rst_type == HardReset ) begin
      fips_csrng_q.delete();
      overflow_condition = 0;
      `DV_CHECK_FATAL(ral.observe_fifo_depth.observe_fifo_depth.predict('b0))
      // fw_ov_wr_fifo_full goes high when the module is disabled.
      precon_fifo_full = 1;
      precon_fifo_cnt = 1;
      // Ignore any outstanding alerts.
      ignore_exp_alert = 1;
    end

    // Internal repetition counters and watermark registers are cleared on enable.
    if (rst_type == Enable) begin
      fork
        begin
          // Clear watermark registers (to 0) and internal repetition counters (to 1).
          `DV_CHECK_FATAL(ral.repcnt_hi_watermarks.fips_watermark.predict(16'd0))
          `DV_CHECK_FATAL(ral.repcnt_hi_watermarks.bypass_watermark.predict(16'd0))
          repcnt_event_cnt = 16'd1;
          `DV_CHECK_FATAL(ral.repcnts_hi_watermarks.fips_watermark.predict(16'd0))
          `DV_CHECK_FATAL(ral.repcnts_hi_watermarks.bypass_watermark.predict(16'd0))
          repcnts_event_cnt = 16'd1;
          // Wait one clock cycle, then propagate the internal counter to the watermark registers.
          cfg.clk_rst_vif.wait_clks(1);
          propagate_repcnt_to_watermark();
        end
      join_none
    end

    // Internal repetition counters are reset to 0 on reset.
    if (rst_type == HardReset) begin
      repcnt_event_cnt = '0;
      repcnts_event_cnt = '0;
    end

    // The SHA3 engine is the one unit that is not always cleared on
    // disable.
    // It clears itself in on disable in normal RNG mode.
    // However, in FW_OV mode it only clears itself
    // when a digest is output or on hard reset so in this case,
    // we leave the sha_process_q alone to represent the fact
    // that there is still data in the SHA3 state.
    //
    // However any entropy absorbed in raw mode (and stashed in
    // raw_process_q), will always be lost on disable.
    if(rst_type == HardReset) begin
      sha_process_q.delete();
      raw_process_q.delete();
      repack_idx_fw_ov = 0;
      intr_test = '0;
      intr_test_active = 0;
      regwen_pending = 0;
    end

    if (rst_type == Disable) begin
      raw_process_q.delete();
    end

    if (rst_type == FWOVDisable) begin
      // For FW_OV mode the 64 bit packer is also cleared.
      repack_idx_fw_ov = 0;
    end

    if ((rst_type == FIFOClr) || (rst_type == Enable)) begin
      observe_fifo_q.delete();
      entropy_data_q.delete();
      // The overflow condition for the observe FIFO is cleared whenever the observe FIFO
      // gets cleared.
      observe_fifo_overflow = 0;
      overflow_read_cnt = 0;
      // Clear variables used for observe FIFO depth prediction.
      observe_push_busy_addr_phase = 0;
      observe_push_busy = 0;
      // Clear variables used for predicting entropy drops.
      post_ht_drops = 0;
      esbit_fifo_processed = 1;
      esbit_last_full_cycle = 0;
      postht_fifo_processed = 1;
      postht_last_full_cycle = 0;
      distr_fifo_processed = 1;
      observe_fifo_processed = 1;
      bypass_fifo_processed = 1;
      precon_fifo_processed = 1;
      sha3_ready_predicted = 1;
      fw_ov_sha3_started = 0;
      esrng_fifo_q.delete();
      esbit_fifo_q.delete();
      postht_fifo_q.delete();
      distr_fifo_q.delete();
      distr_to_observe_fifo_q.delete();
      distr_to_bypass_fifo_q.delete();
      distr_to_precon_fifo_q.delete();
    end

    // reset all other statistics
    threshold_alert_active = 0;
    main_sm_escalates = 0;

    seed_idx = 0;
    seed_tl_read_cnt = 0;

    for (int i = 0; i < RNG_BUS_WIDTH; i++) begin
      `uvm_info(`gfn, "Set REPCNTS cntr", UVM_DEBUG)
      repcnt[i] = (rst_type == HardReset) ? 0 :
                  (rst_type == Enable) ? 1 :
                  repcnt[i];
    end
    repcnt_symbol     = 1;

    prev_rng_val      = '0;

    // Clear records of repcnt/repnts failures
    continuous_fail_count     = 0;
    cont_fail_in_last_sample  = 0;

    // Reset the total_seeds_consumed count.
    cfg.total_seeds_consumed = 0;

    // Clear interrupt state
    known_intr_state                         = 0;
    intr_en_mask                             = 0;

    expected_obsfifo_entries_since_last_intr = 0;

    // After this event, all other inputs from the RNG interface will be discarded by the DUT
    // so we flush this queue to reflect the fact that the DUT will not be folding these into
    // outputs.
    rng_fifo.flush();
    // Note the CSRNG TLM analysis fifo should NOT be flushed, as it contains actual DUT
    // outputs which must be scoreboarded

    `uvm_info(`gfn, $sformatf("%s Detected", rst_type.name), UVM_MEDIUM)
  endfunction

  // Update our behavioral predictions based on new interrupts
  // from_csr: 1 if the new information was observed from the intr_state register
  //           0 if it was observed from the interrupt pins
  function void handle_new_interrupts(bit [NumEntropySrcIntr - 1:0] new_events,
                                      bit from_csr);
    string msg;

    if (new_events[ObserveFifoReady]) begin
      bit [6:0] obs_fifo_threshold =
          ral.observe_fifo_thresh.observe_fifo_thresh.get_mirrored_value();
      bit valid_thresh = ((obs_fifo_threshold <= ObserveFifoDepth) && (obs_fifo_threshold != 0));
      msg = $sformatf("No ObsFifo interrupts should be rec'd for threshold 0x%0h",
                      obs_fifo_threshold);
      `DV_CHECK_FATAL(valid_thresh, msg)
      expected_obsfifo_entries_since_last_intr = int'(obs_fifo_threshold);
      msg = $sformatf("Expecting at least 0x%0h new obsfifo entries",
                      expected_obsfifo_entries_since_last_intr);
      `uvm_info(`gfn, msg, UVM_FULL)
    end
    known_intr_state = known_intr_state | new_events;
  endfunction

  function void clear_interrupts(bit [NumEntropySrcIntr - 1:0] clear_mask);
    known_intr_state &= ~clear_mask;
    intr_test &= ~clear_mask;
    `uvm_info(`gfn, $sformatf("clear_mask: %01h", clear_mask), UVM_FULL)
    `uvm_info(`gfn, $sformatf("known_data: %01h", known_intr_state), UVM_FULL)
  endfunction

  task process_interrupts();
    entropy_src_intr_e i;
    bit [NumEntropySrcIntr - 1:0] new_intrs;
    `uvm_info(`gfn, "STARTING INTERRUPT SCOREBOARD LOOP", UVM_DEBUG)
    forever begin
      `uvm_info(`gfn, "WAITING FOR INTERRUPT", UVM_DEBUG)
      @(interrupt_vif.pins);
      new_intrs = interrupt_vif.pins & ~known_intr_state;
      handle_new_interrupts(new_intrs, 0);
      for (i = i.first(); i < i.last(); i = i.next()) begin
        if (cfg.en_cov)
          cov.intr_pins_cg.sample(i, interrupt_vif.pins[i]);
        if (new_intrs[i]) begin
          `uvm_info(`gfn, $sformatf("INTERRUPT RECEIVED: %0s", i.name), UVM_FULL)
        end
      end
    end
  endtask

  task process_xht();
    // Process XHT transactions.
    forever begin
      @(cfg.m_xht_agent_cfg.vif.mon_cb);
      if (cfg.under_reset) continue;

      if (cfg.xht_only_default_rsp) begin
        // If the environment is configured to maintain the default XHT response at all time, ensure
        // that this is really the case.
        `DV_CHECK_EQ(cfg.m_xht_agent_cfg.vif.mon_cb.rsp,
                     entropy_src_pkg::ENTROPY_SRC_XHT_RSP_DEFAULT)
      end
    end
  endtask

  // All the HT threshold registers are one-way: they can only become more strict unless
  // the DUT is reset.  This function encapsulates this behavior.
  //
  // This function operates on full TL_DW words, with some knowledge of the structure of each
  // register.
  // 1. These registers are consist of two 16b thresholds a bypass and a FIPS threshold.
  //    The one-way restriction is applied to them independently.
  // 2. Both thresholds have the same directional restriction: both can go up or both can go down.
  // If the structure of these registers ever becomes more varied we will have to generalize this
  // function, using structural cues from the RAL model
  //
  // new_val:       The value to be written to the register
  // prev_val:      The current value of the register
  // increase_only: 1 if the register values are allowed to increase.
  //
  // Returns the new predicted value for the register.
  function void predict_one_way_threshold(uvm_reg csr,
                                          bit [TL_DW - 1:0] write_val,
                                          bit increase_only);

    localparam int ThreshW = 16;
    bit [TL_DW - 1:0] prev_val = `gmv(csr);
    int offset                 = csr.get_offset();
    bit [ThreshW - 1:0] new_thresh, prev_thresh, thresh_out;
    bit [TL_DW - 1:0]   result;
    int                 i;
    string              msg, fmt;

    for (i=0; i < TL_DW; i+=ThreshW) begin
      bit is_fips_thresh = (i==0);
      bit update_rejected;
      new_thresh  = write_val[i +: ThreshW];
      prev_thresh =  prev_val[i +: ThreshW];
      thresh_out  = increase_only ? (new_thresh > prev_thresh ? new_thresh : prev_thresh) :
                                    (new_thresh < prev_thresh ? new_thresh : prev_thresh);
      update_rejected = (thresh_out != new_thresh);
      result[i +: ThreshW] = thresh_out;
      cov_vif.cg_one_way_ht_threshold_reg_sample(offset, update_rejected, is_fips_thresh);
    end
    fmt = "Threshold Reg Update. Offset: %08x (%s), Orig: %08x, New: %08x, Final: %08x";
    msg = $sformatf(fmt, offset, prev_val, increase_only ? "INCREASES" : "DECREASES",
                    write_val, result);
    `uvm_info(`gfn, msg, UVM_DEBUG);
    void'(csr.predict(.value(result), .kind(UVM_PREDICT_WRITE)));
  endfunction

  // Function to check for correct values to register fields with mandatory redundancy
  // (i.e. MultiBit boolean values or the ALERT_THRESHOLD register).
  //
  // Performs several scoreboarding functions:
  // It checks that the recently written (mirrored) value is valid. If invalid, the function:
  // - Expects a recovereable alert
  // - Updates the prediction for the RECOV_ALERT_STS register
  // - Samples the relevant coverpoint for recoverable alert events.
  //
  // Arguments:
  // reg_name: the register to check
  // mubi_field: the specific field to examine (when checking for bad MuBi's)
  // sts_field_name: the name of the field to assert
  // which_mubi: The associated coverpoint value to assert when a bad
  //             redundancy is discovered. (includes bad writes to alert threshold
  //             as well as all MuBi fields).
  virtual function void check_redundancy_val(string reg_name, string mubi_field,
                                            string sts_field_name, invalid_mubi_e which_mubi);
    bit bad_redundancy;
    // Check the currently predicted value for the desired register and field
    //
    // Almost all of the redundant values are isolated MultiBit Booleans except for
    // ALERT_THRESHOLD in which the threhold field must equal the inverse of the
    // inverse threshold field.
    if (reg_name != "alert_threshold") begin
      bad_redundancy = mubi4_test_invalid(
          mubi4_t'(get_reg_fld_mirror_value(ral, reg_name, mubi_field)));
    end else begin
      bit [15:0] thresh     = get_reg_fld_mirror_value(ral, "alert_threshold", "alert_threshold");
      bit [15:0] thresh_inv = get_reg_fld_mirror_value(ral, "alert_threshold",
                                                       "alert_threshold_inv");
      bad_redundancy = (thresh != ~thresh_inv);
    end

    if (bad_redundancy) begin
      uvm_reg_field sts_field = ral.recov_alert_sts.get_field_by_name(sts_field_name);
      `DV_CHECK_FATAL(sts_field.predict(.value(1'b1), .kind(UVM_PREDICT_READ)))
      set_exp_alert(.alert_name("recov_alert"), .is_fatal(0));
      cov_vif.cg_mubi_err_sample(which_mubi);
    end
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit do_read_check       = 1'b1;
    // Identifies a register as a one-way threshold (they can only get tighter until reset)
    bit one_way_threshold   = 1'b0;
    // Specifies the direction of the one-way threshold
    bit threshold_increases = 1'b0;
    bit locked_reg_access   = 1'b0;
    bit dut_reg_locked, sw_regupd, module_enabled;
    bit write               = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
    string msg;

    dut_reg_locked = ~`gmv(ral.regwen.regwen);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        // We do not predict the interrupt_state, as there are too many
        // asynchronous events.
        // We also specially control the clearing of these bits
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
      "rev": begin
      end
      "module_enable": begin
      end
      "conf": begin
        locked_reg_access = dut_reg_locked;
      end
      "rev": begin
      end
      "entropy_control": begin
        locked_reg_access = dut_reg_locked;
      end
      "entropy_data": begin
      end
      "health_test_windows": begin
        locked_reg_access = dut_reg_locked;
      end
      "repcnt_thresholds": begin
        locked_reg_access   = dut_reg_locked;
        one_way_threshold   = 1;
        threshold_increases = 0;
      end
      "repcnts_thresholds": begin
        locked_reg_access = dut_reg_locked;
        one_way_threshold   = 1;
        threshold_increases = 0;
      end
      "adaptp_hi_thresholds": begin
        locked_reg_access = dut_reg_locked;
        one_way_threshold   = 1;
        threshold_increases = 0;
      end
      "adaptp_lo_thresholds": begin
        locked_reg_access = dut_reg_locked;
        one_way_threshold   = 1;
        threshold_increases = 1;
      end
      "bucket_thresholds": begin
        locked_reg_access = dut_reg_locked;
        one_way_threshold   = 1;
        threshold_increases = 0;
      end
      "markov_hi_thresholds": begin
        locked_reg_access = dut_reg_locked;
        one_way_threshold   = 1;
        threshold_increases = 0;
      end
      "markov_lo_thresholds": begin
        locked_reg_access = dut_reg_locked;
        one_way_threshold   = 1;
        threshold_increases = 1;
      end
      "repcnt_hi_watermarks": begin
      end
      "repcnts_hi_watermarks": begin
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
        locked_reg_access = dut_reg_locked;
      end
      "alert_summary_fail_counts": begin
      end
      "alert_fail_counts": begin
      end
      "extht_fail_counts": begin
      end
      "fw_ov_control": begin
        locked_reg_access = dut_reg_locked;
      end
      "fw_ov_sha3_start": begin
      end
      "fw_ov_rd_data": begin
        if (!write && channel == AddrChannel) begin
          // Signal that a read is incoming.
          // The actual comparison in the scoreboard happens with a delay. In the DUT the
          // observe FIFO would have been already popped in this cycle. We model this
          // by allowing our observe FIFO queue in the scoreboard to hold one additional
          // word.
          observe_read_incoming = 1;
          `DV_CHECK_FATAL(ral.observe_fifo_depth.observe_fifo_depth.predict(
              `gmv(ral.observe_fifo_depth.observe_fifo_depth)-1, .kind(UVM_PREDICT_DIRECT)))
          // If there's an overflow condition and we only have one word left in the observe FIFO,
          // this means that the overflow condition ends here. Here we signal the end of the
          // overflow condition and update the predictions.
          if (overflow_condition && (observe_fifo_q.size() == 1)) begin
            overflow_condition = 0;
            `DV_CHECK_FATAL(ral.fw_ov_rd_fifo_overflow.fw_ov_rd_fifo_overflow.predict(1'b0))
          end
        end
      end
      "fw_ov_wr_data": begin
      end
      "fw_ov_wr_fifo_full": begin
        if (!write && channel == AddrChannel) begin
          fork
            begin
              bit es_fw_ov_insert_mode, es_bypass_mode, module_enable;
              // Wait for the variables, needed for prediction, to update.
              es_fw_ov_insert_mode = (`gmv(ral.fw_ov_control.fw_ov_mode) == MuBi4True) &&
                  (cfg.otp_en_es_fw_over == MuBi8True) &&
                  (`gmv(ral.fw_ov_control.fw_ov_entropy_insert) == MuBi4True);
              es_bypass_mode = (`gmv(ral.conf.fips_enable) != MuBi4True) ||
                  ((`gmv(ral.entropy_control.es_type) == MuBi4True) &&
                  (`gmv(ral.entropy_control.es_route) == MuBi4True));
              module_enable = (`gmv(ral.module_enable.module_enable) == MuBi4True);

              // fw_ov_wr_fifo_full should only be high if we are in the FW override insert mode,
              // not in bypass mode, the SHA3 is not in the idle state and the precon FIFO is full.
              if (es_fw_ov_insert_mode && ((!es_bypass_mode && precon_fifo_full_q) ||
                  !module_enable)) begin
                fw_ov_wr_fifo_full_prediction = 'b1;
              end else begin
                fw_ov_wr_fifo_full_prediction = 'b0;
              end
            end
          join_none
          do_read_check = 1'b0;
        end
      end
      "fw_ov_rd_fifo_overflow": begin
      end
      "observe_fifo_thresh": begin
        locked_reg_access = dut_reg_locked;
      end
      "observe_fifo_depth": begin
        // If a word is being pushed into the observe FIFO while reading observe_fifo_depth, the
        // prediction will be off by one word. We need to take this into account for predictions.
        if (!write && channel == AddrChannel) begin
          observe_push_busy_addr_phase = observe_push_busy;
        end
      end
      "debug_status": begin
      end
      "recov_alert_sts": begin
      end
      "err_code": begin
      end
      "err_code_test": begin
      end
      "main_sm_state": begin
        do_read_check = 1'b0;
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    if (channel == AddrChannel) begin
      // if incoming access is a write to a valid csr, then make updates right away
      if (write) begin
        if (csr.get_name() == "module_enable") begin
          uvm_reg_data_t reg_data;
          logic [3:0] tl_data_lsbs;
          csr_rd(.ptr(ral.main_sm_state.main_sm_state), .value(reg_data), .backdoor(1));
          tl_data_lsbs = item.get_written_data();
          cov_vif.cg_sw_disable_sample(
              ral.me_regwen.me_regwen.get_mirrored_value(),
              tl_data_lsbs == MuBi4True,
              entropy_src_main_sm_pkg::state_e'(reg_data)
          );
        end
        if (locked_reg_access) begin
          string msg = $sformatf("Attempt to write while locked: %s", csr.get_name());
          `uvm_info(`gfn, msg, UVM_FULL)
          // Cover sw_update_sample if this if the new data represents an attempted change
          // to the previous value (one that can be confirmed by a follow-up read).
          if (item.a_data != `gmv(csr)) begin
            cov_vif.cg_sw_update_sample(
                csr.get_offset(),
                ral.sw_regupd.sw_regupd.get_mirrored_value(),
                ral.module_enable.module_enable.get_mirrored_value() == MuBi4True
            );
          end
        end else begin
          string msg = $sformatf("Unlocked write to: %s", csr.get_name());
          `uvm_info(`gfn, msg, UVM_FULL)
          if (one_way_threshold) begin
            predict_one_way_threshold(csr, item.a_data, threshold_increases);
          end else begin
            `DV_CHECK(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
          end
          // Special handling for registers with broader impacts
          case (csr.get_name())
            "intr_state": begin
              `uvm_info(`gfn, $sformatf("Attempting to clear bits: %01h", item.a_data), UVM_FULL)
              clear_interrupts(item.a_data);
              // If an interrupt condition persists, it will clear at the
              // pins for one cycle before reasserting.
              // Thus there is no need to confirm that it had been immediately reasserted.
            end
            "intr_enable": begin
              intr_en_mask = item.a_data;
            end
            "intr_test": begin
               intr_test = item.a_data;
               intr_test_active = 1;
            end
            "sw_regupd": begin
              bit sw_regupd;
              sw_regupd = `gmv(ral.sw_regupd.sw_regupd);
              if (!sw_regupd) begin
                `DV_CHECK_FATAL(ral.regwen.regwen.predict(.value(0), .kind(UVM_PREDICT_READ)));
              end
            end
            "module_enable": begin
              string msg;
              bit do_disable, do_enable;
              uvm_reg_field enable_field = csr.get_field_by_name("module_enable");
              mubi4_t enable_mubi = mubi4_t'(enable_field.get_mirrored_value());
              do_enable  = (enable_mubi == MuBi4True);
              // Though non-mubi values sent alerts, for the
              // purposes of enablement, all invalid values are effectively disables.
              do_disable = ~do_enable;
              check_redundancy_val("module_enable", "module_enable",
                                   "module_enable_field_alert", invalid_module_enable);

              msg = $sformatf("locked? %01d", dut_reg_locked);
              `uvm_info(`gfn, msg, UVM_FULL)
              fork
                if (do_enable) begin
                  cfg.clk_rst_vif.wait_clks(2);
                  fw_ov_pipe_enabled = 1;
                end
                if (do_enable && !dut_pipeline_enabled) begin
                  dut_pipeline_enabled = 1;
                  handle_disable_reset(Enable);
                  fifos_cleared = 0;
                  collect_entropy();
                  // The DUT internals could take as long as three clocks to clear.
                  cfg.clk_rst_vif.wait_clks(3);
                  handle_disable_reset(Disable);
                end
                begin
                  bit regwen_obs, sw_regupd;
                  int obs_delay = 0;
                  `uvm_info(`gfn, "Waiting for regwen", UVM_FULL)
                  regwen_pending = 1;
                  // Don't update the regwen prediction immediately as the DUT will enforce
                  // delays in REGWEN until it has safely cleared its internal state.  Silently
                  // peek-poll (with watchdog) here until the change in regwen occurs and then
                  // update the prediction.
                  `DV_SPINWAIT(forever begin
                    sw_regupd = `gmv(ral.sw_regupd.sw_regupd);
                    if (!sw_regupd) break; // Device will be conlusively locked via sw_regupd
                    regwen_obs = csr_peek(.ptr(ral.regwen.regwen));
                    if (regwen_obs == do_disable) break;
                    cfg.clk_rst_vif.wait_clks(1);
                    obs_delay++;
                  end)
                  msg = $sformatf("REGWEN update observed after %d clocks", obs_delay);
                  `uvm_info(`gfn, msg, UVM_FULL)
                  `DV_CHECK_FATAL(ral.regwen.regwen.predict(.value(do_disable & sw_regupd),
                                                            .kind(UVM_PREDICT_READ)));
                  regwen_pending = 0;
                  `uvm_info(`gfn, "Waiting for regwen complete", UVM_FULL)
                end
              join_none

              if (do_disable && dut_pipeline_enabled) begin
                // The DUT does not immediately turn off the RNG input. We wait a few cycles to
                // let any last couple RNG samples come into the dut (so we know to delete them
                // from our model of the DUT);
                int base_shutdown_dly = cfg.tlul_to_rng_disable_delay;

                // Send shutdown signals to the various event loops, with delays as necessary
                // to account for empirical pipeline delays in the DUT.
                fork : background_process
                  begin
                    bit rng_bit_enable = (`gmv(ral.conf.rng_bit_enable) == MuBi4True);
                    int rng_shutdown_dly = base_shutdown_dly;
                    cfg.clk_rst_vif.wait_clks(rng_shutdown_dly);
                    dut_pipeline_enabled = 0;
                  end
                  begin
                    int fw_ov_shutdown_dly = base_shutdown_dly;
                    fw_ov_shutdown_dly += 3;
                    cfg.clk_rst_vif.wait_clks(fw_ov_shutdown_dly);
                    fw_ov_pipe_enabled = 0;
                    `uvm_info(`gfn, "FW_OV pipeline clearing", UVM_FULL)
                    handle_disable_reset(FWOVDisable);
                  end
                  begin
                    cfg.clk_rst_vif.wait_clks(cfg.tlul_to_fifo_clr_delay);
                    handle_disable_reset(FIFOClr);
                    fifos_cleared = 1;
                  end
                join_none : background_process
              end
            end
            "conf": begin
              check_redundancy_val("conf", "fips_enable", "fips_enable_field_alert",
                                   invalid_fips_enable);
              check_redundancy_val("conf", "entropy_data_reg_enable",
                                   "entropy_data_reg_en_field_alert",
                                   invalid_entropy_data_reg_enable);
              check_redundancy_val("conf", "fips_flag", "fips_flag_field_alert",
                                   invalid_fips_flag);
              check_redundancy_val("conf", "rng_fips", "rng_fips_field_alert",
                                   invalid_rng_fips);
              check_redundancy_val("conf", "threshold_scope", "threshold_scope_field_alert",
                                   invalid_threshold_scope);
              check_redundancy_val("conf", "rng_bit_enable", "rng_bit_enable_field_alert",
                                   invalid_rng_bit_enable);
              // The `fips_enable` field affects the bypass/FIPS mode selection, so we have to
              // propagate the internal counter to the watermark register.
              propagate_repcnt_to_watermark();
            end
            "entropy_control": begin
              check_redundancy_val("entropy_control", "es_route", "es_route_field_alert",
                                   invalid_es_route);
              check_redundancy_val("entropy_control", "es_type", "es_type_field_alert",
                                   invalid_es_type);
              // Both fields affect the bypass/FIPS mode selection, so we have to propagate the
              // internal counter to the watermark register.
              propagate_repcnt_to_watermark();
            end
            "alert_threshold": begin
              cov_vif.cg_alert_cnt_sample(item.a_data, 0);
              check_redundancy_val("alert_threshold", "", "es_thresh_cfg_alert",
                                   invalid_alert_threshold);
            end
            "fw_ov_control": begin
              check_redundancy_val("fw_ov_control", "fw_ov_mode", "fw_ov_mode_field_alert",
                                   invalid_fw_ov_mode);
              check_redundancy_val("fw_ov_control", "fw_ov_entropy_insert",
                                   "fw_ov_entropy_insert_field_alert",
                                    invalid_fw_ov_entropy_insert);
            end
            "fw_ov_sha3_start": begin
              // The fw_ov_sha3_start field triggers the internal processing of SHA data
              mubi4_t start_mubi  = mubi4_t'(
                  ral.fw_ov_sha3_start.fw_ov_insert_start.get_mirrored_value());
              bit fips_enabled    = ral.conf.fips_enable.get_mirrored_value() == MuBi4True;
              bit es_route        = ral.entropy_control.es_route.get_mirrored_value() == MuBi4True;
              bit es_type         = ral.entropy_control.es_type.get_mirrored_value() == MuBi4True;
              bit is_fips_mode    = fips_enabled && !(es_route && es_type);
              mubi4_t fw_ov_mubi  = mubi4_t'(ral.fw_ov_control.fw_ov_mode.get_mirrored_value());

              bit fw_ov_mode      = (cfg.otp_en_es_fw_over == MuBi8True) &&
                                    (fw_ov_mubi == MuBi4True);
              mubi4_t insert_mubi = mubi4_t'(
                  ral.fw_ov_control.fw_ov_entropy_insert.get_mirrored_value());
              bit fw_ov_insert    = fw_ov_mode && (insert_mubi == MuBi4True);
              bit do_disable_sha  = fw_ov_sha_enabled && (start_mubi == MuBi4False);

              bit write_forbidden = is_fips_mode ? cfg.precon_fifo_vif.write_forbidden :
                                                   cfg.bypass_fifo_vif.write_forbidden;

              check_redundancy_val("fw_ov_sha3_start", "fw_ov_insert_start",
                                   "fw_ov_sha3_start_field_alert", invalid_fw_ov_insert_start);

              // Disabling the fw_ov_sha3_start field triggers the conditioner, but only
              // if the DUT is configured properly.
              if (is_fips_mode && fw_ov_insert && do_disable_sha) begin
                uvm_reg_field recov_sts_fld = ral.recov_alert_sts.es_fw_ov_disable_alert;
                if (fw_ov_pipe_enabled) begin
                  if (write_forbidden) begin
                    // SW _shouldn't_ turn off the SHA3 processing until the last data word
                    // has been processed.  However if it _does_, we should note an alert.
                    // We can also make an accurate prediction of the output (to pass our sims).
                    //
                    // Process the entropy EXCEPT for the last stuck word
                    // which we load into the next round.
                    bit [SHACondWidth - 1:0] sha_temp = sha_process_q.pop_back();
                    `uvm_info(`gfn, "SHA3 disabled for FW_OV (Illegally, data present)", UVM_FULL)
                    // Signal to predict_fw_ov_wr_full() that SHA3 has been started by firmware.
                    fw_ov_sha3_started = 1;
                    package_and_release_entropy();
                    sha_process_q.push_back(sha_temp);
                    `uvm_info(`gfn, "SHA3 disabled while data pending, expecting alert", UVM_MEDIUM)
                    set_exp_alert(.alert_name("recov_alert"), .is_fatal(0));
                    `DV_CHECK_FATAL(recov_sts_fld.predict(.value(1'b1), .kind(UVM_PREDICT_READ)));
                  end else begin
                    `uvm_info(`gfn, "SHA3 disabled for FW_OV (Legally)", UVM_FULL)
                    // Signal to predict_fw_ov_wr_full() that SHA3 has been started by firmware.
                    fw_ov_sha3_started = 1;
                    package_and_release_entropy();
                  end
                end else begin
                  // SHA is disabled while the DUT is disabled.
                  // Another Illegal use case, one that doesn't even process the data.
                  // Expect an alert even though the dut won't do anything with it
                  set_exp_alert(.alert_name("recov_alert"), .is_fatal(0));
                  `DV_CHECK_FATAL(recov_sts_fld.predict(.value(1'b1), .kind(UVM_PREDICT_READ)));
                    `uvm_info(`gfn, "SHA3 disabled for FW_OV (Illegally, disabled)", UVM_FULL)
                end
              end
              fw_ov_sha_enabled = (start_mubi == MuBi4True);
              if (fw_ov_sha_enabled && fw_ov_insert) begin
                `uvm_info(`gfn, "SHA3 enabled for FW_OV", UVM_HIGH)
              end
            end
            "fw_ov_wr_data": begin
              bit module_enabled =
                  ral.module_enable.module_enable.get_mirrored_value() == MuBi4True;
              bit predict_conditioned = do_condition_data();
              bit fw_ov_entropy_insert =
                  (cfg.otp_en_es_fw_over == MuBi8True) &&
                  (ral.fw_ov_control.fw_ov_mode.get_mirrored_value() == MuBi4True) &&
                  (ral.fw_ov_control.fw_ov_entropy_insert.get_mirrored_value() == MuBi4True);

              if (ignore_fw_ov_data_pulse) begin
                msg = $sformatf("fw_ov_wr_data dropped: 0x%08x", item.a_data);
                `uvm_info(`gfn, msg, UVM_FULL)
              end else begin
                msg = $sformatf("fw_ov_wr_data captured: 0x%08x", item.a_data);
                `uvm_info(`gfn, msg, UVM_FULL)
              end

              if (fw_ov_pipe_enabled && fw_ov_entropy_insert && !ignore_fw_ov_data_pulse) begin
                msg = $sformatf("Inserting word 0x%08x into pipeline", item.a_data);
                `uvm_info(`gfn, msg, UVM_MEDIUM)
                // Add this TL-word to the running SHA word
                repacked_entropy_fw_ov = {item.a_data,
                                          repacked_entropy_fw_ov[TL_DW +: (SHACondWidth - TL_DW)]};
                repack_idx_fw_ov++;
                `uvm_info(`gfn, $sformatf("repack_idx_fw_ov: %016x", repack_idx_fw_ov), UVM_HIGH)
                if (repack_idx_fw_ov == SHACondWidth/TL_DW) begin
                  repack_idx_fw_ov = 0;
                  msg = $sformatf("fw_ov SHA word: %016x", repacked_entropy_fw_ov);
                  `uvm_info(`gfn, msg, UVM_HIGH)
                  if (predict_conditioned) begin
                    sha_process_q.push_back(repacked_entropy_fw_ov);
                  end
                end
                // In bypass mode, data is automatically released when a full seed is acquired
                if (!predict_conditioned) begin
                  raw_process_q.push_back(item.a_data);
                  if (raw_process_q.size() == (CSRNG_BUS_WIDTH / TL_DW)) begin
                    package_and_release_entropy();
                  end
                end
              end

              // Count the number of words in the precon FIFO.
              // When module_enabled is low the the FIFO is cleared. When precon_fifo_full_q
              // is high we dropped the current word. Otherwise, the FIFO is not full yet and/or
              // has been popped since it was last in the full state.
              precon_fifo_cnt = !module_enabled ? 0 :
                                precon_fifo_full_q ? precon_fifo_cnt :
                                (precon_fifo_cnt == 2) ? 1 : precon_fifo_cnt + 1;
              // Notify predict_fw_ov_wr_full() that fw_ov_wr_fifo_full is being read.
              predict_fw_ov_wr_fifo_full = 1;
            end
            "err_code_test": begin
              uvm_reg_field err_code_test = csr.get_field_by_name("err_code_test");
              bit [TL_DW - 1:0] err_code = ral.err_code.get_mirrored_value();
              bit[4:0] bit_num = err_code_test.get_mirrored_value();
              bit [TL_DW - 1:0] mask = (32'h1 << bit_num);
              bit is_fatal = 0;
              bit is_logged = 0;
              string msg;
              msg = $sformatf("Received write to ERR_CODE_TEST: %d", bit_num);
              `uvm_info(`gfn, msg, UVM_MEDIUM)
              err_code = err_code | mask;
              msg = $sformatf("Predicted value of ERR_CODE: %08x", err_code);
              `uvm_info(`gfn, msg, UVM_MEDIUM)
              case(bit_num)
                22: begin // es_cntr_err
                  is_fatal = 1;
                  is_logged = 1;
                  main_sm_escalates = 1;
                end
                0, 1, 2, 20, 21, 28, 29, 30: begin // other valid err_code bits
                  // These test bits correspond to events that are always logged
                  // in err_code, but only create fatal alerts if they occur
                  // when the DUT is enabled
                  is_logged = 1;
                  is_fatal = (ral.module_enable.module_enable.get_mirrored_value() == MuBi4True);
                end
                default: begin // all others
                  is_fatal = 0;
                  is_logged = 0;
                end
              endcase
              msg = $sformatf("FATAL: %d, LOGGED: %d", is_fatal, is_logged);
              `uvm_info(`gfn, msg, UVM_MEDIUM)
              if (is_logged) begin
                `DV_CHECK_FATAL(ral.err_code.predict(.value(err_code), .kind(UVM_PREDICT_READ)));
              end
              if (is_fatal) begin
                cov_vif.cg_err_test_sample(bit_num);
                set_exp_alert(.alert_name("fatal_alert"), .is_fatal(1));
              end
              fork
                // Implementation timing detail:
                // If a particular error is escalated it also becomes a main_sm error.
                if (main_sm_escalates) begin
                  int main_sm_err_mask = 1 << 21;
                  cfg.clk_rst_vif.wait_clks(1);
                  err_code |= main_sm_err_mask;
                  `DV_CHECK_FATAL(ral.err_code.predict(.value(err_code), .kind(UVM_PREDICT_READ)));
                end
              join_none
            end
            default: begin
            end
          endcase
        end
      end
    end

    // On reads, if do_read_check is set, then check mirrored_value against item.d_data
    if (!write && channel == DataChannel) begin
      case (csr.get_name())
        "intr_state": begin
          // Though we do not predict the interrupt state we do stop here to process any
          // new activity on any interrupt lines that happen to be disabled.
          // (The enabled ones will be processed as soon as they are seen on the
          // interrupt pins.)
          bit [NumEntropySrcIntr - 1:0] new_events = '0;
          bit [NumEntropySrcIntr - 1:0] to_handle = '0;
          entropy_src_intr_e i;
          new_events = item.d_data & ~known_intr_state;
          to_handle = new_events & ~intr_en_mask;
          if (cfg.en_cov) begin
            for (i = i.first(); i < i.last(); i = i.next()) begin
              // Don't sample int_cg if this was triggered as a test, only if it showed up
              // in normal operation.
              if(!intr_test_active) begin
                cov.intr_cg.sample(i, intr_en_mask[i], item.d_data[i]);
              end
              if(intr_test_active) begin
                cov.intr_test_cg.sample(i, intr_test[i], intr_en_mask[i], item.d_data[i]);
              end
              // Sample cov.inter_pins_cg in process_interrupts()
            end // for (i = i.first(); i < i.last(); i = i.next())
          end
          handle_new_interrupts(to_handle, 1);
        end
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
        "observe_fifo_depth": begin
          // If a new word was pushed to the observe FIFO in the address phase,
          // the prediction is off by 1 word.
          item.d_data -= observe_push_busy_addr_phase;
        end
        "fw_ov_rd_data": begin
          if (fifos_cleared) begin
            `DV_CHECK_FATAL(csr.predict(.value('0), .kind(UVM_PREDICT_READ)))
          end else begin
            // The read check already happens in process_observe_fifo_csr_access().
            do_read_check = 0;
            process_observe_fifo_csr_access(item, csr);
            // Assume (for now) that there is no underflow
            // (We are not tracking it at this time, and so an underflow
            // will kill the simulation.)
            expected_obsfifo_entries_since_last_intr--;
            if (expected_obsfifo_entries_since_last_intr == 0) begin
              // We have successfully received an interrupt and
              // read OBSERVE_FIFO_THRESH entries from the fifo.
              // We can mark this value of OBSERVE_FIFO_THRESH
              // as successful
              bit [6:0] obs_fifo_threshold =
                  ral.observe_fifo_thresh.observe_fifo_thresh.get_mirrored_value();
              cov_vif.cg_observe_fifo_threshold_sample(obs_fifo_threshold);
            end
          end
        end
        "fw_ov_wr_fifo_full": begin
          do_read_check = 1'b0;
          `DV_CHECK_EQ(fw_ov_wr_fifo_full_prediction, item.d_data,
                      $sformatf("reg name: %0s", csr.get_full_name()))
        end
        "recov_alert_sts": begin
          for (int i=0; i < TL_DW; i++) begin
            if (item.d_data[i]) begin
              cov_vif.cg_recov_alert_sample(i);
            end
          end
        end
        default: begin
        end
      endcase

      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
    end
  endtask

  task monitor_fw_ov_write_exceptions(virtual entropy_subsys_fifo_exception_if#(1) vif,
                                      bit active_in_fips_mode);
    bit fw_ov_mode, fw_ov_insert, fips_enabled, es_route, es_type, is_fips_mode;
    int i;

    forever begin
      @(vif.mon_cb);

      fw_ov_mode   = (cfg.otp_en_es_fw_over == MuBi8True) &&
                     (`gmv(ral.fw_ov_control.fw_ov_mode) == MuBi4True);
      fw_ov_insert = fw_ov_mode && (`gmv(ral.fw_ov_control.fw_ov_entropy_insert) == MuBi4True);
      fips_enabled = `gmv(ral.conf.fips_enable) == MuBi4True;
      es_route     = `gmv(ral.entropy_control.es_route) == MuBi4True;
      es_type      = `gmv(ral.entropy_control.es_type) == MuBi4True;
      is_fips_mode = fips_enabled && !(es_route && es_type);

      // If we are not in FW_OV mode at this time, then this error event doesn't matter.
      // (Such events seem to happen in normal HW-driven operation, but they do not
      // reflect errors, as the HW chain has proper flow control)
      if (!fw_ov_insert) continue;

      // This fifo event also does matter if the FIFO is currently not active for FW_OV/FIPS mode
      if (active_in_fips_mode ^ is_fips_mode) continue;

      for (i=0; i<N_FIFO_ERR_TYPES; i++) begin
        if (vif.mon_cb.error_pulses[i]) begin
          case (i)
            FIFO_WRITE_ERR: begin
              if (!under_alert_handshake["recov_alert"]) begin
                uvm_reg_field fld = ral.recov_alert_sts.es_fw_ov_wr_alert;
                `DV_CHECK_FATAL(fld.predict(1'b1, .kind(UVM_PREDICT_READ)));
                set_exp_alert("recov_alert");
              end
              // Make a single-clock pulse to tell the TL process that this error has been
              // identified and the ongoing write should be ignored.
              ignore_fw_ov_data_pulse = 1;
              fork
                begin
                  @(vif.mon_cb);
                  // Clear the last pulse (unless there is another event right behind the last
                  // one)
                  if (!vif.mon_cb.error_pulses[FIFO_WRITE_ERR]) begin
                    ignore_fw_ov_data_pulse = 0;
                  end
                end
              join_none
            end
            default: begin
              // ignore other types as this FIFO has proper HW flow control at the other end.
            end
          endcase
        end
      end
    end
  endtask

  task process_fifo_exceptions();
    fork
      // The FW_OV_WR_DATA register is connected to the precon fifo in FIPS mode and the bypass
      // FIFO in bypass mode.  Monitor them both for exceptions.
      monitor_fw_ov_write_exceptions(cfg.precon_fifo_vif, 1);
      monitor_fw_ov_write_exceptions(cfg.bypass_fifo_vif, 0);
    join_none
  endtask

  function bit [FIPS_BUS_WIDTH - 1:0] get_fips_compliance(
      bit [FIPS_CSRNG_BUS_WIDTH - 1:0] fips_csrng);
    return fips_csrng[CSRNG_BUS_WIDTH +: FIPS_BUS_WIDTH];
  endfunction

  function bit [CSRNG_BUS_WIDTH - 1:0] get_csrng_seed(bit [FIPS_CSRNG_BUS_WIDTH - 1:0] fips_csrng);
    return fips_csrng[0 +: CSRNG_BUS_WIDTH];
  endfunction

  function bit do_condition_data();
    bit             route_sw;
    bit             sw_bypass;
    bit             fips_enable;
    bit             is_fips_mode;
    bit             predict_conditioned;

    route_sw    = (`gmv(ral.entropy_control.es_route) == MuBi4True);
    sw_bypass   = (`gmv(ral.entropy_control.es_type)  == MuBi4True);
    fips_enable = (`gmv(ral.conf.fips_enable)         == MuBi4True);

    is_fips_mode = fips_enable && !(route_sw && sw_bypass);

    predict_conditioned = is_fips_mode;

    return predict_conditioned;

  endfunction


  // Note: this routine is destructive in that it empties the input argument
  function bit [FIPS_CSRNG_BUS_WIDTH - 1:0] predict_fips_csrng();
    bit [FIPS_CSRNG_BUS_WIDTH - 1:0] fips_csrng_data;
    bit [CSRNG_BUS_WIDTH - 1:0]      csrng_data;
    bit [FIPS_BUS_WIDTH - 1:0]       fips_data;
    bit                              predict_conditioned;
    mubi4_t                          rng_single_bit;

    int                              sample_frames;

    string                           msg, fmt;

    predict_conditioned = do_condition_data();

    rng_single_bit = mubi4_t'(`gmv(ral.conf.rng_bit_enable));

    sample_frames = predict_conditioned ? sha_process_q.size() : raw_process_q.size;

    fmt = "processing %01d 64-bit frames in %s mode";
    msg = $sformatf(fmt, sample_frames, predict_conditioned ? "FIPS" : "BYPASS");

    `uvm_info(`gfn, msg, UVM_FULL);

    fips_data = (`gmv(ral.conf.fips_flag) == MuBi4True) &&
                (`gmv(ral.module_enable.module_enable) == MuBi4True);

    if (predict_conditioned) begin
      localparam int BytesPerSHAWord = SHACondWidth / 8;

      bit [7:0] sha_msg[];
      bit [7:0] sha_digest[CSRNG_BUS_WIDTH / 8];
      longint msg_len = 0;

      sha_msg = new[sha_process_q.size() * BytesPerSHAWord];

      // The DUT's SHA engine takes data in 64 (SHACondWidth) bit chunks, whereas the DPI call
      // requires an array of bytes.  Here we break the SHA-words into a stream of bytes
      while (sha_process_q.size() > 0) begin
        bit [SHACondWidth - 1:0] sha_word    = '0;
        bit [7:0] sha_byte                   = '0;
        sha_word = sha_process_q.pop_front();
        for (int i = 0; i < BytesPerSHAWord; i++) begin
          sha_byte = sha_word[ 0 +: 8];
          sha_word = sha_word >> 8;
          `uvm_info(`gfn, $sformatf("msglen: %04h, byte: %02h", msg_len, sha_byte), UVM_FULL)
          sha_msg[msg_len] = sha_byte;
          msg_len++;
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

      while (raw_process_q.size() > 0) begin
        bit [TL_DW - 1:0] word = raw_process_q.pop_front();
        string fmt;

        fmt = "sample size: %01d, last elem.: %08h";
        `uvm_info(`gfn, $sformatf(fmt, raw_process_q.size()+1, word), UVM_FULL)

        csrng_data = csrng_data >> TL_DW;
        csrng_data[CSRNG_BUS_WIDTH - TL_DW +: TL_DW] = word;
      end
      `uvm_info(`gfn, $sformatf("Unconditioned data: %096h", csrng_data), UVM_HIGH)
    end

    fips_csrng_data = {fips_data, csrng_data};

    return fips_csrng_data;
  endfunction

  task wait_enabled();
    if (!dut_pipeline_enabled) begin
      wait(dut_pipeline_enabled);
      `uvm_info(`gfn, "Enable detected", UVM_MEDIUM)
    end
  endtask

  virtual task process_esrng_fifo();
    bit [3:0] esrng_rd_data;
    bit [3:0] postht_wr_data;
    bit esbit_wr_data;
    bit bit_sel_enable;
    int rng_bit_sel;
    forever begin
      @(posedge cfg.clk_rst_vif.clk);
      if(!cfg.en_scb) begin
        continue;
      end
      // Wait to see if something is going to be pushed into esrng_fifo_q.
      `DV_SPINWAIT_EXIT(wait(esrng_fifo_q.size());,
                        cfg.clk_rst_vif.wait_n_clks(1);)
      // If esrng_fifo_q is still empty at the negedge, we can skip to the next cycle.
      if (esrng_fifo_q.size() == 0) begin
        continue;
      end

      bit_sel_enable = (`gmv(ral.conf.rng_bit_enable) == MuBi4True);
      rng_bit_sel = `gmv(ral.conf.rng_bit_sel);
      // Always pop, if the following FIFOs are full we drop the entropy.
      esrng_rd_data = esrng_fifo_q.pop_front();

      // In single lane mode, we push into the esbit FIFO if it has space left.
      if (bit_sel_enable && (esbit_fifo_q.size() < 4) && !esbit_last_full_cycle) begin
        // Wait for the esbit FIFO to be done such that the words we push into it
        // are handled in the next cycle.
        wait(esbit_fifo_processed);
        esbit_fifo_q.push_back(esrng_rd_data[rng_bit_sel]);
      // In the normal mode, we push into the postht FIFO if it has space left.
      end else if (!bit_sel_enable && (postht_fifo_q.size() < 8) && !postht_last_full_cycle) begin
        // Wait for the postht FIFO to be done such that the words we push into it
        // are handled in the next cycle.
        wait(postht_fifo_processed);
        postht_fifo_q.push_back(esrng_rd_data);
      // Otherwise we drop the entropy and increase the counter. We also predict an alert.
      end else begin
        post_ht_drops += 1;
        `DV_CHECK_FATAL(ral.recov_alert_sts.postht_entropy_drop_alert.predict(1'b1));
        set_exp_alert(.alert_name("recov_alert"), .is_fatal(0), .max_delay(cfg.alert_max_delay));
      end
    end
  endtask

  virtual task process_esbit_fifo();
    bit esbit_rd_data;
    bit [3:0] postht_wr_data;
    bit bit_sel_enable;
    forever begin
      @(posedge cfg.clk_rst_vif.clk);
      if(!cfg.en_scb) begin
        continue;
      end

      bit_sel_enable = (`gmv(ral.conf.rng_bit_enable) == MuBi4True);
      // If we are not in single lane mode or the postht FIFO is full we don't do anything.
      // Since this is a packer FIFO we need to wait until we have a full word before we pop.
      if (!bit_sel_enable || (postht_fifo_q.size() >= 8) ||
          postht_last_full_cycle || (esbit_fifo_q.size() < 4)) begin
        // Signal to the esrng FIFO that we are done processing for the current cycle.
        esbit_fifo_processed = 1;
        @(negedge cfg.clk_rst_vif.clk);
        esbit_fifo_processed = 0;
        continue;
      end
      // Wait for the postht FIFO to be done such that the words we push into it
      // are handled in the next cycle.
      wait(postht_fifo_processed);
      // Signal to the preceding esrng FIFO that the full signal will be high for one cycle.
      esbit_last_full_cycle = 1;
      while (esbit_fifo_q.size()) begin
        esbit_rd_data = esbit_fifo_q.pop_front();
        postht_wr_data = {esbit_rd_data, postht_wr_data[1 +: 3]};
      end
      postht_fifo_q.push_back(postht_wr_data);
      // Signal to the esrng FIFO that we are done processing for the current cycle.
      esbit_fifo_processed = 1;
      @(negedge cfg.clk_rst_vif.clk);
      esbit_fifo_processed = 0;
      esbit_last_full_cycle = 0;
    end
  endtask

  virtual task process_postht_fifo();
    bit [3:0] postht_rd_data;
    bit [TL_DW - 1:0] distr_wr_data;
    forever begin
      @(posedge cfg.clk_rst_vif.clk);
      if(!cfg.en_scb) begin
        continue;
      end

      // If the distr FIFO is full we model backpressure by not doing anything.
      // Since this is a packer FIFO we need to wait until we have a full word before we pop.
      if ((distr_fifo_q.size() >= 2) || (postht_fifo_q.size() < 8)) begin
        // Signal to the preceding FIFOs that we are done processing for the current cycle.
        postht_fifo_processed = 1;
        @(negedge cfg.clk_rst_vif.clk);
        postht_fifo_processed = 0;
        continue;
      end
      // Signal to the preceding FIFOs that the full signal will be high for one cycle.
      postht_last_full_cycle = 1;
      while (postht_fifo_q.size()) begin
        postht_rd_data = postht_fifo_q.pop_front();
        distr_wr_data = {postht_rd_data, distr_wr_data[4 +: (TL_DW - 4)]};
      end
      distr_fifo_q.push_back(distr_wr_data);

      // Signal to the preceding FIFOs that we are done processing for the current cycle.
      postht_fifo_processed = 1;
      @(negedge cfg.clk_rst_vif.clk);
      postht_fifo_processed = 0;
      postht_last_full_cycle = 0;
    end
  endtask

  virtual task process_distr_fifo();
    bit [TL_DW - 1:0] distr_rd_data;
    bit predict_conditioning, fw_ov_mode, fw_ov_insert;
    forever begin
      @(posedge cfg.clk_rst_vif.clk);
      if(!cfg.en_scb) begin
        continue;
      end
      // Since the distr FIFO is configured in feedthrough mode, we wait for the postht FIFO
      // and immediately process the entropy.
      wait(postht_fifo_processed);

      predict_conditioning = do_condition_data();
      fw_ov_mode   = (cfg.otp_en_es_fw_over == MuBi8True) &&
                     (`gmv(ral.fw_ov_control.fw_ov_mode) == MuBi4True);
      fw_ov_insert = fw_ov_mode && (`gmv(ral.fw_ov_control.fw_ov_entropy_insert) == MuBi4True);

      // If the conditioner is being used and we are not in fw_ov_insert mode,
      // then we only propagate the entropy if the distr FIFO is not full.
      if ((predict_conditioning && !fw_ov_insert && (distr_to_precon_fifo_q.size() >= 2)) ||
          (distr_fifo_q.size() == 0)) begin
        // Signal to the preceding FIFOs that we are done processing for the current cycle.
        distr_fifo_processed = 1;
        @(negedge cfg.clk_rst_vif.clk);
        distr_fifo_processed = 0;
        continue;
      end

      // Distribute the entropy to the respective FIFOs depending on the operational mode.
      distr_rd_data = distr_fifo_q.pop_front();
      if (fw_ov_mode) begin
        distr_to_observe_fifo_q.push_back(distr_rd_data);
      end
      if (!predict_conditioning && !fw_ov_insert) begin
        distr_to_bypass_fifo_q.push_back(distr_rd_data);
      end
      if (predict_conditioning && !fw_ov_insert) begin
        distr_to_precon_fifo_q.push_back(distr_rd_data);
      end

      // Signal to the preceding FIFOs that we are done processing for the current cycle.
      distr_fifo_processed = 1;
      @(negedge cfg.clk_rst_vif.clk);
      distr_fifo_processed = 0;
    end
  endtask

  virtual task process_observe_fifo();
    bit [TL_DW - 1:0] observe_wr_data;
    forever begin
      @(posedge cfg.clk_rst_vif.clk);
      if(!cfg.en_scb) begin
        continue;
      end
      // In case of an overflow condition, we predict the end of the condition right at
      // the posedge so we need wait and see if it ends in this cycle.
      `DV_SPINWAIT_EXIT(wait(!overflow_condition);,
                        cfg.clk_rst_vif.wait_n_clks(1);)

      // If the observe queue is receiving entropy, process it.
      if (distr_to_observe_fifo_q.size()) begin
        observe_wr_data = distr_to_observe_fifo_q.pop_front();
        // If there is an overflow condition ongoing, we drop the entropy.
        // Otherwise we process it here.
        if (!overflow_condition) begin
          // If the observe FIFO is just about to overflow, we need to wait to see if a read
          // happens in the same cycle. Otherwise we wrongly predict an overflow.
          `DV_SPINWAIT_EXIT(wait(observe_read_incoming);,
                            wait(!cfg.clk_rst_vif.clk);)
          // If the observe FIFO has overflown signal the overflow condition and predict the
          // fw_ov_rd_fifo_overflow register to be set to true. We drop the overflowing data by
          // not pushing into the observe FIFO queue.
          if (observe_fifo_q.size() >= (OBSERVE_FIFO_DEPTH + observe_read_incoming)) begin
            overflow_condition = 1;
            `DV_CHECK_FATAL(ral.fw_ov_rd_fifo_overflow.fw_ov_rd_fifo_overflow.predict('b1))

          // If there is no overflow condition going on then push the repacked entropy into the
          // observe FIFO queue.
          end else begin
            observe_fifo_q.push_back(observe_wr_data);
            // Signal to potential reads to observe_fifo_depth that a word is currently being pushed
            // into the observe FIFO.
            fork
              begin
                observe_push_busy = 1;
                wait(!ral.observe_fifo_depth.is_busy());
                observe_push_busy = 0;
                `DV_CHECK_FATAL(ral.observe_fifo_depth.observe_fifo_depth.predict(
                    `gmv(ral.observe_fifo_depth.observe_fifo_depth)+1, .kind(UVM_PREDICT_DIRECT)))
              end
            join_none
          end
        end
      end

      // Signal to the preceding FIFOs that we are done processing for the current cycle.
      observe_fifo_processed = 1;
      wait(!cfg.clk_rst_vif.clk);
      observe_fifo_processed = 0;
    end
  endtask

  virtual task process_bypass_fifo();
    bit [TL_DW - 1:0] bypass_wr_data;
    bit predict_conditioning, fw_ov_mode, fw_ov_insert;
    forever begin
      @(posedge cfg.clk_rst_vif.clk);
      if(!cfg.en_scb) begin
        continue;
      end

      predict_conditioning = do_condition_data();
      fw_ov_mode   = (cfg.otp_en_es_fw_over == MuBi8True) &&
                     (`gmv(ral.fw_ov_control.fw_ov_mode) == MuBi4True);
      fw_ov_insert = fw_ov_mode && (`gmv(ral.fw_ov_control.fw_ov_entropy_insert) == MuBi4True);

      if (!fw_ov_insert && !predict_conditioning && distr_to_bypass_fifo_q.size()) begin
        // Get the data for redistribution.
        bypass_wr_data = distr_to_bypass_fifo_q.pop_front();
        raw_process_q.push_back(bypass_wr_data);
        if (raw_process_q.size() == 12) begin
          package_and_release_entropy();
        end
      end

      // Signal to the preceding FIFOs that we are done processing for the current cycle.
      bypass_fifo_processed = 1;
      @(negedge cfg.clk_rst_vif.clk);
      bypass_fifo_processed = 0;
    end
  endtask

  virtual task process_precon_fifo();
    bit [TL_DW - 1:0] precon_rd_data;
    bit [SHACondWidth:0] repacked_entropy_sha;
    bit predict_conditioning, fw_ov_mode, fw_ov_insert;
    string msg;
    forever begin
      @(posedge cfg.clk_rst_vif.clk);
      if(!cfg.en_scb) begin
        continue;
      end
      // Wait for the prediction of the sha3_ready signal.
      // This signal will tell us if SHA3 is ready to absorb entropy.
      wait(sha3_ready_predicted);

      predict_conditioning = do_condition_data();
      fw_ov_mode   = (cfg.otp_en_es_fw_over == MuBi8True) &&
                     (`gmv(ral.fw_ov_control.fw_ov_mode) == MuBi4True);
      fw_ov_insert = fw_ov_mode && (`gmv(ral.fw_ov_control.fw_ov_entropy_insert) == MuBi4True);

      // If the conditioner is not being used or the data for the conditioner comes from firmware,
      // we don't need to do anything.
      if (fw_ov_insert || !predict_conditioning || !sha3_msg_ready ||
          (distr_to_precon_fifo_q.size() < 2)) begin
        // Signal to the preceding FIFOs that we are done processing for the current cycle.
        precon_fifo_processed = 1;
        @(negedge cfg.clk_rst_vif.clk);
        precon_fifo_processed = 0;
        continue;
      end
      // Push the entropy into the SHA3 processing queue.
      while (distr_to_precon_fifo_q.size()) begin
        precon_rd_data = distr_to_precon_fifo_q.pop_front();
        repacked_entropy_sha = {precon_rd_data,
                                repacked_entropy_sha[TL_DW +: (SHACondWidth - TL_DW)]};
      end
      sha_process_q.push_back(repacked_entropy_sha);

      // Signal to the preceding FIFOs that we are done processing for the current cycle.
      precon_fifo_processed = 1;
      @(negedge cfg.clk_rst_vif.clk);
      precon_fifo_processed = 0;
    end
  endtask

  task collect_entropy();
    bit disable_detected;

    wait_enabled();

    forever begin : collect_entropy_loop
      push_pull_item#(.HostDataWidth(RNG_BUS_WIDTH)) rng_item;
      `DV_SPINWAIT_EXIT(rng_fifo.peek(rng_item);,
                        wait(!dut_pipeline_enabled);)
      disable_detected = (!rng_fifo.try_get(rng_item) || !dut_pipeline_enabled);
      if (disable_detected) return;
      esrng_fifo_q.push_back(rng_item.h_data);
      health_test_data_q.push_back(rng_item.h_data);
    end
  endtask

  // Propagate internal repetition counter to watermark register.  Call this function when changing
  // a setting that influences the switch between bypass and FIPS mode.  This will propagate the
  // internal repetition counters to the watermark field of the new mode (i.e., bypass or FIPS).
  function automatic void propagate_repcnt_to_watermark();
    bit fips_enable, bypass_to_sw, route_to_sw, bypass_mode, rng_bit_en;
    bit [1:0] rng_bit_sel;
    int max_repcnt = 0;
    // Determine whether FIPS or bypass mode is now active.
    fips_enable = `gmv(ral.conf.fips_enable) == MuBi4True;
    bypass_to_sw = `gmv(ral.entropy_control.es_type) == MuBi4True;
    route_to_sw = `gmv(ral.entropy_control.es_route) == MuBi4True;
    rng_bit_en  = (`gmv(ral.conf.rng_bit_enable) == MuBi4True);
    rng_bit_sel = `gmv(ral.conf.rng_bit_sel);
    bypass_mode = ~fips_enable | (bypass_to_sw & route_to_sw);
    // Calculate the new value for repcnt_event_cnt, since it can change when we toggle rng_bit_en.
    for (int i = 0; i < RNG_BUS_WIDTH; i++) begin
      max_repcnt = (repcnt[i] > max_repcnt) ? repcnt[i] : max_repcnt;
    end
    repcnt_event_cnt = rng_bit_en ? repcnt[rng_bit_sel] : max_repcnt;
    if (bypass_mode) begin
      // Propagate internal repetition counter to bypass watermark fields.
      if (repcnt_event_cnt > `gmv(ral.repcnt_hi_watermarks.bypass_watermark)) begin
        `DV_CHECK_FATAL(ral.repcnt_hi_watermarks.bypass_watermark.predict(repcnt_event_cnt))
      end
      if (repcnts_event_cnt > `gmv(ral.repcnts_hi_watermarks.bypass_watermark)) begin
        `DV_CHECK_FATAL(ral.repcnts_hi_watermarks.bypass_watermark.predict(repcnts_event_cnt))
      end
    end else begin
      // Propagate internal repetition counter to FIPS watermark fields.
      if (repcnt_event_cnt > `gmv(ral.repcnt_hi_watermarks.fips_watermark)) begin
        `DV_CHECK_FATAL(ral.repcnt_hi_watermarks.fips_watermark.predict(repcnt_event_cnt))
      end
      if (repcnts_event_cnt > `gmv(ral.repcnts_hi_watermarks.fips_watermark)) begin
        `DV_CHECK_FATAL(ral.repcnts_hi_watermarks.fips_watermark.predict(repcnts_event_cnt))
      end
    end
  endfunction

  task health_test_scoring_thread();
    bit [15:0]                window_size;
    entropy_phase_e           dut_fsm_phase;
    int                       window_rng_frames;
    int                       pass_requirement, pass_count, startup_fail_count;
    bit                       fw_ov_insert;
    bit                       is_fips_mode;
    bit                       fips_enable, es_route, es_type;
    bit                       rng_bit_en;
    bit [1:0]                 rng_bit_sel;
    int                       failures_in_window;
    rng_val_t                 rng_val;
    queue_of_rng_val_t        window;

    string                    msg;

    forever begin : simulation_loop
      entropy_src_xht_item xht_item;
      bit disable_detected = 0;

      wait_enabled();

      fips_enable = (`gmv(ral.conf.fips_enable)         == MuBi4True);
      es_route    = (`gmv(ral.entropy_control.es_route) == MuBi4True);
      es_type     = (`gmv(ral.entropy_control.es_type)  == MuBi4True);
      rng_bit_en  = (`gmv(ral.conf.rng_bit_enable)      == MuBi4True);
      rng_bit_sel = `gmv(ral.conf.rng_bit_sel);

      is_fips_mode  = fips_enable && !(es_route && es_type);

      fw_ov_insert = (cfg.otp_en_es_fw_over == MuBi8True) &&
                     (`gmv(ral.fw_ov_control.fw_ov_mode) == MuBi4True) &&
                     (`gmv(ral.fw_ov_control.fw_ov_entropy_insert) == MuBi4True);

      pass_count = 0;
      startup_fail_count = 0;
      seed_idx = 0;

      forever begin : enabled_loop

        window.delete();

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
            // When in the post-boot, halted state the DUT will continue to monitor health checks,
            // but not output CSRNG data or data to the TL ENTROPY_DATA register.
            // In this cass the pass_requirement and ht_fips_mode values don't mean anything
            pass_requirement = 0;
            ht_fips_mode     = 0;
          end
          default: begin
            `uvm_fatal(`gfn, "Invalid predicted dut state (bug in environment)")
          end
        endcase

        `uvm_info(`gfn, $sformatf("phase: %s\n", dut_fsm_phase.name), UVM_HIGH)

        window_size = rng_window_size(seed_idx, is_fips_mode, fw_ov_insert,
                                      `gmv(ral.health_test_windows.fips_window) * RNG_BUS_WIDTH);

        `uvm_info(`gfn, $sformatf("window_size: %08d\n", window_size), UVM_HIGH)

        // Note on RNG bit enable and window frame count:
        // When rng_bit_enable is selected, the function below repacks the data so that
        // the selected bit fills a whole frame.
        // This mirrors the DUT's behavior of repacking the data before the health checks
        //
        // Thus the number of window frames 4 times as large when the bit select is enabled.

        window_rng_frames = rng_bit_en ? window_size : (window_size / RNG_BUS_WIDTH);

        forever begin : window_loop
          string fmt;
          bit [RNG_BUS_WIDTH - 1:0] xht_bus_val;

          // For synchronization purposes we wait to process each sample until it is visible on the
          // as an event on xht bus. We then perform checks to ensure that the xht interface data
          // matches the RNG data and that the window boundaries (as seen on the XHT bus) appear
          // at the correct times.
          //
          // TODO(#16276): perform a more complete check of the other XHT outputs.
          //
          forever begin : sample_loop
            // Wait either for the next xht_item, or wait at most two clocks
            // after a disable event.
            `DV_SPINWAIT_EXIT(xht_fifo.peek(xht_item);,
                              wait(!dut_pipeline_enabled);
                              cfg.clk_rst_vif.wait_clks(2);)
            disable_detected = !xht_fifo.try_get(xht_item);
            if (disable_detected) break; // No events. DUT has shutdown
            if (!xht_item.req.clear) begin
              evaluate_external_ht(xht_item.rsp, ht_fips_mode);
            end
            if (xht_item.req.entropy_bit_valid || xht_item.req.window_wrap_pulse) break;
          end : sample_loop

          if (disable_detected) break; // No sample events. DUT has shutdown

          // In case of entropy drops, there is more entropy to be health tested than the usual
          // window_rng_frames.
          if (xht_item.req.window_wrap_pulse) begin
            `DV_CHECK(window.size() == (window_rng_frames + post_ht_drops))
            post_ht_drops = 0;
            break;
          end else begin
            `DV_CHECK(window.size() < (window_rng_frames + post_ht_drops))
          end
          // Check whether the rng_bit_en and the rng_bit_sel match the values in the CONF register.
          `DV_CHECK(xht_item.req.rng_bit_en == rng_bit_en)
          `DV_CHECK(xht_item.req.rng_bit_sel == rng_bit_sel)

          // No shutdown, or window close pulse, must be a sample.
          `DV_CHECK(xht_item.req.entropy_bit_valid)

          // Make sure that RNG data has been received and that it matches the
          // ExtHT data
          `DV_CHECK(health_test_data_q.size() > 0)
          rng_val = health_test_data_q.pop_front();

          `DV_CHECK(xht_item.req.entropy_bit == rng_val)
          window.push_back(rng_val);

          fmt = "RNG element: %0x, idx: %0d";
          `uvm_info(`gfn, $sformatf(fmt, rng_val, window.size()), UVM_FULL)

          // Update the repetition counts, which are updated continuously.
          // The other health checks only operate on complete windows, and are processed later.
          update_repcnts(ht_fips_mode, rng_val);
        end

        if (disable_detected) break; // No events. DUT has shutdown

        // Process end of window events
        `DV_CHECK(xht_item.req.window_wrap_pulse)

        failures_in_window = health_check_rng_data(window, ht_fips_mode);

        if (failures_in_window > 0) begin
          pass_count = 0;
          // Most failures are handled in the alert counter registers
          // However the startup phase has special handling.
          startup_fail_count++;
        end else begin
          pass_count++;
          if (startup_fail_count < 2) startup_fail_count = 0;
        end

        process_failures(failures_in_window, fw_ov_insert, dut_fsm_phase, startup_fail_count);
        window.delete();

        // Once in the halted state, or in the fw_ov_insert_entropy mode, pre-tested data is
        // discarded after the health checks
        if ((dut_fsm_phase == HALTED) || fw_ov_insert) begin
          continue;
        end

        `uvm_info(`gfn, $sformatf("pass_requirement: %01d", pass_requirement), UVM_HIGH)
        `uvm_info(`gfn, $sformatf("raw_process_q.size: %01d", raw_process_q.size()), UVM_HIGH)
        `uvm_info(`gfn, $sformatf("sha_process_q.size: %01d", sha_process_q.size()), UVM_HIGH)

        if (pass_count >= pass_requirement && !threshold_alert_active && !main_sm_escalates) begin
          // update counters for processing next seed:
          pass_count = 0;
          seed_idx++;
        end
      end : enabled_loop
    end : simulation_loop
  endtask

  function void package_and_release_entropy();
    bit [FIPS_CSRNG_BUS_WIDTH - 1:0] fips_csrng;
    bit [CSRNG_BUS_WIDTH - 1:0] csrng_seed;
    bit entropy_data_reg_enable;

    entropy_data_reg_enable = (cfg.otp_en_es_fw_read == MuBi8True) &&
                              (ral.conf.entropy_data_reg_enable.get_mirrored_value() == MuBi4True);

    `uvm_info(`gfn, $sformatf("raw_process_q.size(): %01d", raw_process_q.size()), UVM_FULL)
    `uvm_info(`gfn, $sformatf("sha_process_q.size(): %01d", sha_process_q.size()), UVM_FULL)
    fips_csrng = predict_fips_csrng();

    // package data for routing to SW and to CSRNG:
    csrng_seed = get_csrng_seed(fips_csrng);

    // Only inject entropy data if entropy data is enabled
    if (entropy_data_reg_enable) begin
      entropy_data_q.push_back(csrng_seed);
    end

    fips_csrng_q.push_back(fips_csrng);

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

      // Check to see whether a recov_alert should be expected
      if (seeds_out != 0 && get_csrng_seed(item.d_data) == prev_csrng_seed) begin
        `uvm_info(`gfn, "Repeated seed, expecting recov_alert", UVM_MEDIUM)
        `DV_CHECK_FATAL(ral.recov_alert_sts.es_bus_cmp_alert.predict(1'b1));
        set_exp_alert(.alert_name("recov_alert"), .is_fatal(0), .max_delay(cfg.alert_max_delay));
      end

      prev_csrng_seed = get_csrng_seed(item.d_data);
      seeds_out++;

      while (fips_csrng_q.size() > 0) begin : seed_trial_loop
        bit [FIPS_CSRNG_BUS_WIDTH - 1:0] prediction;
        // Unlike in the TL case, there is no need to leave seed predictions in the queue.
        prediction = fips_csrng_q.pop_front();
        if (prediction == item.d_data) begin
          csrng_seeds++;
          cfg.total_seeds_consumed++;
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
    string msg, fmt;
    bit fw_ov_enabled = (cfg.otp_en_es_fw_over == MuBi8True) &&
                        (ral.fw_ov_control.fw_ov_mode.get_mirrored_value() == MuBi4True);
    bit drops_allowed;

    csr_val = item.d_data;

    fmt = "Predicting observe FIFO access, Looking for: %08x";
    msg = $sformatf(fmt, csr_val);
    `uvm_info(`gfn, msg, UVM_FULL)

    // Put the following code inside of a fork to avoid consuming time.
    fork
      if (!fw_ov_enabled) begin
        // if fw_ov mode has never been enabled (and the programming model has been correctly
        // applied) then the observe fifo should be empty and cleared.
        msg = "Observe FIFO is disabled";
        `uvm_info(`gfn, msg, UVM_FULL)
        `DV_CHECK_FATAL(csr.predict(.value('0), .kind(UVM_PREDICT_READ)))
      end else begin
        bit [TL_DW - 1:0] prediction;
        // Pop the observe FIFO queue and compare the prediction to the actual value.
        prediction = observe_fifo_q.pop_front();
        observe_read_incoming = 0;
        fmt = "Predicting observe FIFO access, Comparing to: %08x Actual value: %08x";
        msg = $sformatf(fmt, prediction, csr_val);
        `uvm_info(`gfn, msg, UVM_FULL)
        `DV_CHECK_EQ_FATAL(prediction, csr_val,
            $sformatf("Prediction for observe FIFO access failed."))
        `DV_CHECK_FATAL(csr.predict(.value(prediction), .kind(UVM_PREDICT_READ)))
        observe_fifo_words++;
        cov_vif.cg_observe_fifo_event_sample(
            mubi4_t'(ral.conf.fips_enable.get_mirrored_value()),
            mubi4_t'(ral.conf.fips_flag.get_mirrored_value()),
            mubi4_t'(ral.conf.rng_fips.get_mirrored_value()),
            mubi4_t'(ral.conf.threshold_scope.get_mirrored_value()),
            mubi4_t'(ral.conf.rng_bit_enable.get_mirrored_value()),
            ral.conf.rng_bit_sel.get_mirrored_value(),
            mubi4_t'(ral.entropy_control.es_route.get_mirrored_value()),
            mubi4_t'(ral.entropy_control.es_type.get_mirrored_value()),
            mubi4_t'(ral.conf.entropy_data_reg_enable.get_mirrored_value()),
            mubi8_t'(cfg.otp_en_es_fw_read),
            mubi4_t'(ral.fw_ov_control.fw_ov_mode.get_mirrored_value()),
            mubi8_t'(cfg.otp_en_es_fw_over),
            mubi4_t'(ral.fw_ov_control.fw_ov_entropy_insert.get_mirrored_value())
        );
        msg = $sformatf("Match found: %d\n", observe_fifo_words);
        `uvm_info(`gfn, msg, UVM_FULL)
      end
    join_none
  endfunction

  virtual task predict_fw_ov_wr_full();
    bit [StateWidthPad-1:0] sha3pad_state, sha3pad_state_next;
    bit cs_aes_halt_o;
    bit fips_enabled;
    bit es_route;
    bit es_type;
    bit is_fips_mode;
    bit fw_ov_entropy_insert;
    forever begin
      @(posedge cfg.clk_rst_vif.clk);
      // Wait for a tick to be able to read the updated values of the sha3pad state.
      // Otherwise we will read the values from the previous cycle.
      #1;
      if(!cfg.en_scb) begin
        continue;
      end

      fips_enabled = ral.conf.fips_enable.get_mirrored_value() == MuBi4True;
      es_route     = ral.entropy_control.es_route.get_mirrored_value() == MuBi4True;
      es_type      = ral.entropy_control.es_type.get_mirrored_value() == MuBi4True;
      is_fips_mode = fips_enabled && !(es_route && es_type);

      fw_ov_entropy_insert =
          (cfg.otp_en_es_fw_over == MuBi8True) &&
          (ral.fw_ov_control.fw_ov_mode.get_mirrored_value() == MuBi4True) &&
          (ral.fw_ov_control.fw_ov_entropy_insert.get_mirrored_value() == MuBi4True);

      `DV_CHECK(uvm_hdl_read(pad_st_path, sha3pad_state))
      `DV_CHECK(uvm_hdl_read(pad_st_d_path, sha3pad_state_next))
      `DV_CHECK(uvm_hdl_read(aes_halt_o_path, cs_aes_halt_o))

      // SHA3 only accepts new words if the SHA3 pad SM is the StMessage state and cs_aes_halt_o
      // is low. If the SHA3 pad SM is about to leave the StMessage state, the sha3_nsg_ready
      // signal will go low. This signal is needed to predict whether the precon FIFO is full.
      sha3_msg_ready = (sha3pad_state == StMessage) && (sha3pad_state_next == StMessage);
      sha3_ready_predicted = 1;
      // precon_fifo_full is updated whenever a new word is written to fw_ov_wr_data.
      // The full signal however is needed for prediction with one cycle of delay since
      // pushing/popping the FIFO takes one clock cycle as well.
      precon_fifo_full_q = precon_fifo_full;
      // Predict whether the precon FIFO is full.
      fork
        begin
          `DV_SPINWAIT_EXIT(wait(predict_fw_ov_wr_fifo_full);,
                            cfg.clk_rst_vif.wait_n_clks(1);)
          // If the FIFO has entered the full state, set precon_fifo_full to high.
          if (fw_ov_entropy_insert && is_fips_mode && !sha3_msg_ready &&
              !precon_fifo_full_q && (precon_fifo_cnt == 2) && predict_fw_ov_wr_fifo_full) begin
            // Reset predict_fw_ov_wr_fifo_full for the next time the fw_ov_wr_fifo_full is read.
            predict_fw_ov_wr_fifo_full = 0;
            precon_fifo_full = 1;
            // Wait for sha3_msg_ready and reset precon_fifo_full and precon_fifo_cnt.
            `DV_SPINWAIT_EXIT(wait(sha3_msg_ready);,
                              wait(!dut_pipeline_enabled);)
            // Wait until the SHA3 ready signal is predicted and after one cycle the precon FIFO
            // will be empty again.
            wait(sha3_ready_predicted);
            cfg.clk_rst_vif.wait_clks(1);
            precon_fifo_full = 0;
            precon_fifo_cnt = 0;
          end else begin
            // Reset predict_fw_ov_wr_fifo_full for the next time the fw_ov_wr_fifo_full is read.
            predict_fw_ov_wr_fifo_full = 0;
          end
        end
      join_none
      // Start the SHA3 processing when the SHA3Pad SM enters the StPad state.
      if ((sha3pad_state == StMessage) && (sha3pad_state_next == StPad)) begin
        // Only start the SHA3 if it hasn't already been started via the fw_ov_sha3_start CSR.
        if (!fw_ov_sha3_started) begin
          package_and_release_entropy();
        end
        fw_ov_sha3_started = 0;
      end
      @(negedge cfg.clk_rst_vif.clk);
      sha3_ready_predicted = 0;
    end
  endtask

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
    // Normally at this point a simulation checks that all FIFOs and
    // Queues are empty.  However, for entropy_src, which has no 1-1
    // mapping between inputs and potential output, most of the simulations
    // are time-based not transaction-based.
    //
    // The scoreboard FIFOs are allowed to have some entries at end of sim
    // as these may represent:
    // - unused RNG inputs
    // - unused internal state corresponding to partial seeds
    // - dropped outputs (due to finite buffer space inside the DUT)
    //
    // Entropy Source contains assertions to ensure that bits are only dropped
    // when its internal buffers are full.  These checks depend on DUT internals,
    // so we cannot and do not perform them in the scoreboard.
  endfunction

endclass
