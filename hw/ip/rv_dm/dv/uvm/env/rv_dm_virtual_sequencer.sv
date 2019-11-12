// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_virtual_sequencer extends dv_base_virtual_sequencer #(
    .CFG_T(rv_dm_env_cfg),
    .COV_T(rv_dm_env_cov)
  );
  `uvm_component_utils(rv_dm_virtual_sequencer)

  jtag_sequencer  jtag_sequencer_h;
  tl_sequencer    tl_host_sequencer_h;
  tl_sequencer    tl_device_sequencer_h;

  `uvm_component_new

endclass
