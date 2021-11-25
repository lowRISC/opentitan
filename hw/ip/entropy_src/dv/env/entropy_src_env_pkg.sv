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
    EntropyValid     = 0,
    HealthTestFailed = 1,
    EBusChkFailed    = 2,
    ObserveFifoReady = 3,
    FatalErr         = 4
  } entropy_src_intr_e;

  typedef enum { BOOT, STARTUP, CONTINUOUS } entropy_phase_e;
  typedef bit [RNG_BUS_WIDTH-1:0] rng_val_t;
  typedef rng_val_t queue_of_rng_val_t[$];

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
  function automatic entropy_phase_e convert_seed_idx_to_phase(int seed_idx, bit boot_disable);
    if (!boot_disable) begin
      if (seed_idx == 0) begin
        return BOOT;
      end else if (seed_idx == 1) begin
        return STARTUP;
      end else begin
        return CONTINUOUS;
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
  function automatic int rng_window_size(int seed_idx, bit bypass,
                                         bit boot_disable, int fips_window_size);
    entropy_phase_e phase;

    // Counts the number of seeds that have been successfully generated
    // in any post-boot phase.

    phase = convert_seed_idx_to_phase(seed_idx, boot_disable);

    return (bypass || phase == BOOT) ? entropy_src_pkg::CSRNG_BUS_WIDTH : fips_window_size;

  endfunction

  // return zero if this next set of rng values would cause a health check failure,
  // based on the currently configured thresholds.
  function automatic bit health_check_rng_data(queue_of_rng_val_t sample);
    // TODO: Implement this
    return 0;
  endfunction


  // package sources
  `include "entropy_src_env_cfg.sv"
  `include "entropy_src_env_cov.sv"
  `include "entropy_src_virtual_sequencer.sv"
  `include "entropy_src_scoreboard.sv"
  `include "entropy_src_env.sv"
  `include "entropy_src_vseq_list.sv"

endpackage
