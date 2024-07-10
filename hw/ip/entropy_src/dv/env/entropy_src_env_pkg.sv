// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package entropy_src_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import entropy_src_ral_pkg::*;
  import push_pull_agent_pkg::*;
  import entropy_src_xht_agent_pkg::*;
  import entropy_src_pkg::*;
  import prim_mubi_pkg::*;
  import entropy_subsys_fifo_exception_pkg::*;
  import entropy_src_main_sm_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter bit [TL_DW-1:0]   INCR_ENTROPY_LO    = 32'h76543210;
  parameter bit [TL_DW-1:0]   INCR_ENTROPY_HI    = 32'hfedcba98;
  parameter string            LIST_OF_ALERTS[]   = {"recov_alert","fatal_alert"};
  parameter uint              NUM_ALERTS         = 2;
  parameter uint              OBSERVE_FIFO_DEPTH = 32;

  // types
  typedef enum int {
    EntropyValid      = 0,
    HealthTestFailed  = 1,
    ObserveFifoReady  = 2,
    FatalErr          = 3,
    NumEntropySrcIntr = 4
  } entropy_src_intr_e;

  typedef enum int {
    invalid_fips_enable             = 0,
    invalid_entropy_data_reg_enable = 1,
    invalid_module_enable           = 2,
    invalid_threshold_scope         = 3,
    invalid_rng_bit_enable          = 4,
    invalid_fw_ov_mode              = 5,
    invalid_fw_ov_entropy_insert    = 6,
    invalid_fw_ov_insert_start      = 7,
    invalid_es_route                = 8,
    invalid_es_type                 = 9,
    invalid_alert_threshold         = 10,
    invalid_fips_flag               = 11,
    invalid_rng_fips                = 12
  } invalid_mubi_e;

  typedef enum int {
    sfifo_esrng_err        = 0,
    sfifo_distr_err        = 1,
    sfifo_observe_err      = 2,
    sfifo_esfinal_err      = 3,
    es_ack_sm_err          = 4,
    es_main_sm_err         = 5,
    es_cntr_err            = 6,
    fifo_read_err          = 7,
    fifo_state_err         = 8,
    fifo_cntr_err          = 9,
    sfifo_esrng_err_test   = 10,
    sfifo_distr_err_test   = 11,
    sfifo_observe_err_test = 12,
    sfifo_esfinal_err_test = 13,
    es_ack_sm_err_test     = 14,
    es_main_sm_err_test    = 15,
    es_cntr_err_test       = 16,
    fifo_read_err_test     = 17,
    fifo_state_err_test    = 18
  } err_code_e;

  typedef enum int {
    sfifo_observe_error = 0,
    sfifo_esrng_error   = 1,
    sfifo_distr_error   = 2,
    sfifo_esfinal_error = 3,
    es_ack_sm_error     = 4,
    es_main_sm_error    = 5,
    es_cntr_error       = 6
  } fatal_err_e;

  typedef enum int {
    window_cntr     = 0,
    repcnt_ht_cntr  = 1,
    repcnts_ht_cntr = 2,
    adaptp_ht_cntr  = 3,
    bucket_ht_cntr  = 4,
    markov_ht_cntr  = 5
  } cntr_e;

  typedef enum int {
    repcnt_ht  = 0,
    repcnts_ht = 1,
    adaptp_ht  = 2,
    bucket_ht  = 3,
    markov_ht  = 4
  } health_test_e;

  typedef enum int {
    bypass  = 0,
    fips    = 1
  } health_test_mode_e;

  typedef enum int {
    repcnt_ht_fail = 0,
    adaptp_ht_fail = 1,
    bucket_ht_fail = 2,
    markov_ht_fail = 3
  } ht_fail_e;

  typedef enum int {
    write = 0,
    read  = 1,
    state = 2
  } which_fifo_err_e;

  typedef enum int {
    sfifo_esrng   = 0,
    sfifo_distr   = 1,
    sfifo_observe = 2,
    sfifo_esfinal = 3
  } which_fifo_e;

  typedef enum int {
    high_test = 0,
    low_test  = 1
  } which_ht_e;

  typedef enum bit [4:0] {
    sfifo_esrng_err_code   = 0,
    sfifo_distr_err_code   = 1,
    sfifo_observe_err_code = 2,
    sfifo_esfinal_err_code = 3,
    es_ack_sm_err_code     = 20,
    es_main_sm_err_code    = 21,
    es_cntr_err_code       = 22,
    fifo_write_err_code    = 28,
    fifo_read_err_code     = 29,
    fifo_state_err_code    = 30
  } err_code_test_val_e;


  typedef enum { BOOT, STARTUP, CONTINUOUS, HALTED, ERROR } entropy_phase_e;
  typedef bit [RNG_BUS_WIDTH-1:0] rng_val_t;
  typedef bit [TL_DW-1:0]         tl_val_t;
  typedef rng_val_t queue_of_rng_val_t[$];
  typedef tl_val_t  queue_of_tl_val_t[$];

  //
  // general helper function that converts the "seed index", the number of CSRNG seeds which the DUT
  // has already generated, to a prediction of the current phase.
  //
  // Knowing the phase is important for predicting the response of the entropy source to both
  // input RNG data as well as the behavior it takes during failed health checks.
  //
  // Note a copy of the seed index should be maintained by both the sequence generator and
  // the scoreboard. If a disable event is ever detected, the seed index should be reset to zero,
  // as the DUT's FSM will reset to idle in this case, meaning that it will have to again
  // satisfy both the startup and (optional) boot phases.
  //
  function automatic entropy_phase_e convert_seed_idx_to_phase(int seed_idx,
                                                               bit fips_enable,
                                                               bit fw_ov_insert);

    if (!fips_enable) begin
      if (fw_ov_insert || (seed_idx == 0)) begin
        return BOOT;
      end else begin
        return HALTED;
      end
    end else begin
      if (seed_idx == 0) begin
        return STARTUP;
      end else begin
        return CONTINUOUS;
      end
    end
  endfunction

  //
  // Helper function to determines the proper window_size for the current round of health checks
  // as a function of the seed index.
  //
  // Like like the phase helper function above, this function is required for both scoreboarding and
  // sequence generation.
  //
  // The window size also dictates the ammount of data needed to create a single seed.
  //
  function automatic int rng_window_size(int seed_idx, bit fips_enable, bit fw_ov_insert,
                                         int fips_window_size);
    entropy_phase_e phase;

    // Counts the number of seeds that have been successfully generated
    // in any post-boot phase.

    phase = convert_seed_idx_to_phase(seed_idx, fips_enable, fw_ov_insert);

    return (phase == BOOT || phase == HALTED) ? entropy_src_pkg::CSRNG_BUS_WIDTH : fips_window_size;

  endfunction

  // Determine a random failure time according to an exponential distribution with
  // mean failure time mtbf.
  //
  // The exponential distribution is appropriate for any process where the instantaneous likelihood
  // of failure is the same regardless of how long the device has been active.  For example,
  // if the MTBF is 1s, then the probability of failing in any particular 1 ns period is 1e-9.
  //
  // For more information about the exponential distribution see (for example):
  // https://en.wikipedia.org/wiki/Exponential_distribution
  //

  function automatic realtime randomize_failure_time(realtime mtbf);
    // Random non-zero integer
    int      rand_i;
    // Uniformly distributed random float in range (0, 1].
    // 0 is not included in this range, but 1 is.
    real     rand_r;

    realtime now, random_fail_time;

    if (!std::randomize(rand_i) with {rand_i > 0;}) begin
      return -1;
    end

    rand_r = real'(rand_i)/{$bits(rand_i){1'b1}};

    now = $realtime();

    random_fail_time = now - $ln(rand_r) * mtbf;

    return random_fail_time;
  endfunction // randomize_failure_time

  //
  // Helper function: ideal_threshold_recommendation
  //
  // Purpose:
  // For use when choosing appropriate health test thresholds (specifically for the three
  // windowed health tests: adaptp, markov and bucket) based on the desired failure rate.
  //
  // The function assumes an ideal noise input, and estimates appropriate upper or lower
  // thresholds based on a desired sigma-level (number of standard deviations to exceed
  // when calculating the threshold.
  //
  // Inputs:
  // int    window_size: the number of bits to consider for the test (combining all RNG bus lines)
  // health_test_e test: the test to consider (adaptp_ht, bucket_ht, or markov_ht)
  // bit       per_line: set to 1 if the test is being evaluated on a per_line basis
  //                     (if 0, the range applies if the results are summed over all RNG lines)
  // which_ht_e  hi_low: which threshold to calculate, upper or lower.
  // real desired_sigma: the number of standard deviations to provide within the range.  Assuming
  //                     the window size is large enough to treat the test as normally distributed,
  //                     the probability of the test within the range increases with the number of
  //                     sigma
  //
  // Output:
  // An threshold with the desired certainty of test passing, rounded up for high thresholds,
  // rounded down for low threholds
  //
  // The function computes the mean and standard deviation of the test result, assuming a binomial
  // distribution (or multinomial distribution in the case of the Bucket test).  Then the min/max
  // range is generated assuming that the window size is large enough to apply a gaussian
  // approximation.
  //
  // This base sequence generates a uniform rng sequence (when not failing), the thresholds
  // are generated assuming all bits are equally likely, and there are no correlations of any kind.
  // (e.g. a maximum entropy RNG stream). Derived classes which overload the randomize() method
  // to introduce statistical defects should also overload this function to match the new
  // distribution.
  //
  // This function can be used to generate high and low test thresholds with a desired likelihood
  // of failure
  //
  //      No. of sigma   Approximate probability of test failure ( P(x) = 1 - erf( x / sqrt(2) ))
  //     ------------------------------------------------
  //                 1   31.7%
  //               1.5   13.4%
  //                 2    4.6%
  //               2.5    1.2%
  //                 3   0.27%
  //               3.3    0.1%
  //               3.9    1e-4
  //              4.42    1e-5
  //               4.9    1e-6
  //
  // The table above can be used to estimate the likelihood of failure for the AdaptP and Markov
  // tests, which have both high and low thresholds.  Since the Bucket test has only a single
  // threshold, the likelihood of chance bucket-test failure is 1/2 the above value for the same
  // sigma value.
  //
  // The table above does not account for rounding error. Furthermore, since the approximation to a
  // normal distribution ignores any skew or other higher moments, this leads additional devations
  // from the tabled values particularly for smaller window sizes and at higher sigma values.

  function automatic int ideal_threshold_recommendation(int window_size, health_test_e test,
                                                        bit per_line, which_ht_e hi_low,
                                                        real desired_sigma);
    int n;
    real p, mean, stddev;
    int result, upper_threshold, lower_threshold;
    string msg;

    case(test)
      adaptp_ht: begin
        // number of trials is equal to number of bits, either in the whole window or per line
        n = per_line ? (window_size / RNG_BUS_WIDTH) : window_size;
        p = 0.5;
      end
      bucket_ht: begin
        n = (window_size / RNG_BUS_WIDTH);
        p = 1.0/real'(1 << RNG_BUS_WIDTH);
      end
      markov_ht: begin
        n = per_line ? (window_size / RNG_BUS_WIDTH / 2) : window_size / 2;
        p = 0.5;
      end
      default: begin
        `dv_fatal("Invalid test!", "entropy_src_env_pkg::ideal_threshold_recommendation")
      end
    endcase
    mean   = p * n;
    stddev = $sqrt(p * (1 - p) * n);

    lower_threshold = (test == bucket_ht) ? 0 : $floor(mean - desired_sigma * stddev);
    upper_threshold = $ceil(mean + desired_sigma * stddev);
    // For large values of sigma, the gaussian approximation can recommend thresholds larger than
    // the total number of trials.   In such cases we cap the threshold at the total number of
    // trials for the given test.
    upper_threshold = (upper_threshold > n) ? n : upper_threshold;
    lower_threshold = (lower_threshold < 0) ? 0 : lower_threshold;

    result = (hi_low == high_test) ? upper_threshold : lower_threshold;

    msg = {
        "Threshold Calculation\n",
        $sformatf("window_size: %d\n", window_size),
        $sformatf("test: %s\n", test.name()),
        $sformatf("per_line: %d\n", per_line),
        $sformatf("high or low: %s\n", hi_low.name()),
        $sformatf("desired sigma: %f\n", desired_sigma),
        $sformatf("n: %d, p: %f\n", n, p),
        $sformatf("mean: %f, stddev: %f\n", mean, stddev),
        $sformatf("result: %d\n", result),
        $sformatf("result (hex): 0x%04h\n", result[15:0])
    };

    `uvm_info("entropy_src_env_pkg::ideal_threshold_recommendation", msg, UVM_DEBUG)

    return result;

  endfunction

  // Returns the number of sigma between the threshold and the mean.
  //
  // To be used for calculating the actual sigma-values associated with a threshold when sampling
  // coverpoints. This function is effectively the inverse of ideal_threshold_recommendation.
  //
  function automatic real ideal_threshold_to_sigma(int window_size, health_test_e test,
                                                  bit per_line, which_ht_e hi_low,
                                                  int actual_threshold);
    int n;
    real p, mean, stddev;
    real result, offset;

    case(test)
      adaptp_ht: begin
        // number of trials is equal to number of bits, either in the whole window or per line
        n = per_line ? (window_size / RNG_BUS_WIDTH) : window_size;
        p = 0.5;
      end
      bucket_ht: begin
        n = (window_size / RNG_BUS_WIDTH);
        p = 1.0/real'(1 << RNG_BUS_WIDTH);
      end
      markov_ht: begin
        n = per_line ? (window_size / RNG_BUS_WIDTH / 2) : window_size / 2;
        p = 0.5;
      end
      default: begin
        `dv_fatal("Invalid test!", "entropy_src_env_pkg::ideal_threshold_recommendation")
      end
    endcase
    mean   = p * n;
    stddev = $sqrt(p * (1 - p) * n);

    offset = actual_threshold - mean;

    // Low thresholds should always below the mean.
    // Invert to make offset a positive number (assuming the threshold is on the correct side).
    // NOTE: The bucket test only has a high threshold.
    if ( (hi_low != high_test) && (test != bucket_ht) ) begin
      offset = offset * -1;
    end

    // If offset is less than zero it means that the threshold is beyond the mean.
    // Just count it as zero.
    return (offset < 0) ? 0 : offset / stddev;

  endfunction


  // package sources
  `include "entropy_src_dut_cfg.sv"
  `include "entropy_src_env_cfg.sv"
  `include "entropy_src_env_cov.sv"
  `include "entropy_src_virtual_sequencer.sv"
  `include "entropy_src_scoreboard.sv"
  `include "entropy_src_env.sv"
  `include "entropy_src_vseq_list.sv"

endpackage
