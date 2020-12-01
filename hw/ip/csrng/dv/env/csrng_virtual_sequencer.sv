// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(csrng_env_cfg),
    .COV_T(csrng_env_cov)
  );
  `uvm_component_utils(csrng_virtual_sequencer)

  push_pull_sequencer#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))
    entropy_src_sequencer_h;

  `uvm_component_new

endclass
