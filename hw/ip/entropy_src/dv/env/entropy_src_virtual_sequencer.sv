// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(entropy_src_env_cfg),
    .COV_T(entropy_src_env_cov)
  );
  `uvm_component_utils(entropy_src_virtual_sequencer)

  push_pull_sequencer#(.HostDataWidth(entropy_src_pkg::RNG_BUS_WIDTH))         rng_sequencer_h;
  push_pull_sequencer#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))  csrng_sequencer_h;

  `uvm_component_new

endclass
