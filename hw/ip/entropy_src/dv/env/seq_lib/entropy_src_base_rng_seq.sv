// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Base class for generating non-ideal RNG sequences for entropy_src
//
// Three major features distinguigh this class from its push_pull_indefinite_host_seq baseclass:
// 1. Methods to return the expected mean and standard deviation of the various health checks
// 2. Introduces support for both complete and soft failures of the RNG, with expected (short)
//    lifetimes of hard_mtbf or soft_mtbf.  This base class implements hard failures by
//    freezing the outputs at a random value at some randomly distributed time, as determined by a
//    exponential distibution with a mean time of hard_mtbf.
//    This base class does not generate soft failures, e.g. intolerable statistical deviations
//    from the ideal uniform distribution.  Unless in a hard failure state, the RNG outputs
//    are always ideal.  However, the frame work for the timing soft failures is implemented here.
// 3. The "reset_rng()" method should be used to initialize the sequence, and to bring the sequence
//    back into the typical/good state.  After reset the failure control variables are randomized,
//    to simulate a different future failure.
//
// Extending this class:
//
// This class generates three new methods: random_data_typical, random_data_soft_fail and
// threshold_rec. In order to generate weak failures (or rng streams where the typical performance
// is less than ideal), these methods should be overloaded.
//
// The threshold_rec method should be written assuming that the RNG is operating in the "typical"
// performance mode.

class entropy_src_base_rng_seq extends push_pull_indefinite_host_seq#(
    .HostDataWidth (entropy_src_pkg::RNG_BUS_WIDTH)
  );

  realtime hard_mtbf;
  realtime soft_mtbf;

  `uvm_object_utils_begin(entropy_src_base_rng_seq)
    `uvm_field_real(hard_mtbf, UVM_DEFAULT)
    `uvm_field_real(soft_mtbf, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

   bit is_initialized;

  // Failure bit control: Controls which lines will fail in the next hard failure event
  rand bit [RNG_BUS_WIDTH - 1:0] hard_fail_bit_ctrl;

  // In hard failure, at least one bit must be stuck
  constraint hard_fail_bit_ctrl_c { hard_fail_bit_ctrl != {RNG_BUS_WIDTH{1'b0}};}

  // Failure bit control: Controls the state of any failed RNG lines
  rand bit [RNG_BUS_WIDTH - 1:0] hard_fail_state;

  realtime hard_fail_time, soft_fail_time;
  bit      is_hard_failed, is_soft_failed;

  task reset_rng();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(hard_fail_bit_ctrl);
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(hard_fail_state)

    `uvm_info(`gfn, "Initializing RNG sequence", UVM_MEDIUM)

    if (check_soft_failure()) begin
      `uvm_info(`gfn, "Resetting soft failure", UVM_MEDIUM)
      is_soft_failed = 0;
    end
    soft_fail_time = randomize_failure_time(soft_mtbf);
    `DV_CHECK_FATAL(soft_fail_time >= 0, "Failed to schedule soft failure")

    if (check_hard_failure()) begin
      `uvm_info(`gfn, "Resetting hard failure", UVM_MEDIUM)
      is_hard_failed = 0;
    end
    hard_fail_time = randomize_failure_time(hard_mtbf);
    `DV_CHECK_FATAL(hard_fail_time >= 0, "Failed to schedule hard failure")

    is_initialized = 1;

  endtask

  function bit check_soft_failure();
    bit result;
    result = is_initialized && ($realtime() > soft_fail_time);
    if (!is_soft_failed && result) begin
      `uvm_info(`gfn, "Soft Failure Detected", UVM_MEDIUM)
    end
    is_soft_failed = result;
    return is_soft_failed;
  endfunction

  function bit check_hard_failure();
    bit result;
    result = is_initialized && ($realtime() > hard_fail_time);
    if (!is_hard_failed && result) begin
      `uvm_info(`gfn, "Hard Failure Detected", UVM_MEDIUM)
    end
    is_hard_failed = result;
    return is_hard_failed;
  endfunction

  virtual task pre_body();
    super.pre_body();
    reset_rng();
  endtask

  virtual function rng_val_t random_data_typical();
    rng_val_t next_rng_val;
    `DV_CHECK_STD_RANDOMIZE_FATAL(next_rng_val)
    return next_rng_val;
  endfunction

  virtual function bit [RNG_BUS_WIDTH - 1:0] random_data_soft_fail();
    // For this base class, soft failure is identical
    return random_data_typical();
  endfunction

  virtual function void randomize_item(push_pull_item#(RNG_BUS_WIDTH) item);
    super.randomize_item(item);
    if(check_soft_failure()) begin
      item.h_data = random_data_soft_fail();
    end else begin
      item.h_data = random_data_typical();
    end
    if(check_hard_failure()) begin
      item.h_data = (item.h_data     & ~hard_fail_bit_ctrl) |
                    (hard_fail_state &  hard_fail_bit_ctrl);
    end
  endfunction

  // Function threshold_rec
  //
  // Purpose:
  // For use when choosing appropriate health test thresholds (specifically for the three
  // windowed health tests: adaptp, markov and bucket) based on the desired failure rate.
  //
  // Inputs:
  // int    window_size: the number of bits to consider for the test (combining all RNG bus lines)
  // test_e        test: the test to consider (AdaptP, Bucket, or Markov)
  // bit       per_line: set to 1 if the test is being evaluated on a per_line basis
  //                     (if 0, the range applies if the results are summed over all RNG lines)
  // real desired_sigma: the number of standard deviations to provide within the range.  Assuming
  //                     the window size is large enough to treat the test as normally distributed,
  //                     the probability of the test within the range increases with the number of
  //                     sigma
  //
  // Outputs:
  // lower_threshold, upper_threshold: A min/max threshold pair with the desired certainty of
  // test passing.
  //
  // In this particular baseclass we use the routine ideal_treshold_recommendation from the
  // entropy_src_env_pkg to reflect that, in the absence of hard or soft failures, this baseclass
  // generates Idealized RNG bitstreams.
  //
  // If a child class overrides the random_data_typical method to general non-ideal noise (even
  // during normal operation) this function can be overidden to provide new thresholds which
  // will still provide the desired failure rates even with typical non-idealities taken into
  // account.


  virtual function void threshold_rec(int window_size, health_test_e test, bit per_line,
                                      real desired_sigma, output int lower_threshold,
                                      output int upper_threshold);
    lower_threshold = ideal_threshold_recommendation(window_size, test, per_line, low_test,
                                                     desired_sigma);
    upper_threshold = ideal_threshold_recommendation(window_size, test, per_line, high_test,
                                                     desired_sigma);
  endfunction

endclass
