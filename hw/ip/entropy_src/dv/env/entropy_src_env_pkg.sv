// Copyright lowRISC contributors.
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
  import entropy_src_pkg::*;
  import prim_mubi_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter bit [TL_DW-1:0]   INCR_ENTROPY_LO  = 32'h76543210;
  parameter bit [TL_DW-1:0]   INCR_ENTROPY_HI  = 32'hfedcba98;
  parameter string            LIST_OF_ALERTS[] = {"recov_alert","fatal_alert"};
  parameter uint              NUM_ALERTS       = 2;

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
    invalid_es_route                = 7,
    invalid_es_type                 = 8
  } invalid_mubi_e;

  typedef enum int {
    sfifo_esrng_err        = 0,
    sfifo_observe_err      = 1,
    sfifo_esfinal_err      = 2,
    es_ack_sm_err          = 3,
    es_main_sm_err         = 4,
    es_cntr_err            = 5,
    fifo_write_err         = 6,
    fifo_read_err          = 7,
    fifo_state_err         = 8,
    sfifo_esrng_err_test   = 9,
    sfifo_observe_err_test = 10,
    sfifo_esfinal_err_test = 11,
    es_ack_sm_err_test     = 12,
    es_main_sm_err_test    = 13,
    es_cntr_err_test       = 14,
    fifo_write_err_test    = 15,
    fifo_read_err_test     = 16,
    fifo_state_err_test    = 17
  } err_code_e;

  typedef enum int {
    sfifo_observe_error = 0,
    sfifo_esrng_error   = 1,
    sfifo_esfinal_error = 2,
    es_ack_sm_error     = 3,
    es_main_sm_error    = 4,
    es_cntr_error       = 5
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
    sfifo_observe = 1,
    sfifo_esfinal = 2
  } which_fifo_e;

  typedef enum int {
    high_test = 0,
    low_test  = 1
  } which_ht_e;

  typedef enum { BOOT, STARTUP, CONTINUOUS, HALTED } entropy_phase_e;
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

  // package sources
  `include "entropy_src_env_cfg.sv"
  `include "entropy_src_env_cov.sv"
  `include "entropy_src_virtual_sequencer.sv"
  `include "entropy_src_scoreboard.sv"
  `include "entropy_src_env.sv"
  `include "entropy_src_vseq_list.sv"

endpackage
