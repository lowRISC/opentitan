// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(edn_env_cfg),
    .COV_T(edn_env_cov)
  );
  `uvm_component_utils(edn_virtual_sequencer)

  push_pull_sequencer#(.HostDataWidth(edn_env_pkg::FIPS_ENDPOINT_BUS_WIDTH))
       endpoint_sequencer_h[NUM_ENDPOINTS-1:0];

  `uvm_component_new

endclass
