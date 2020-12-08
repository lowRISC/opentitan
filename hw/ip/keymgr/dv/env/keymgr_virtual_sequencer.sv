// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(keymgr_env_cfg),
    .COV_T(keymgr_env_cov)
  );
  `uvm_component_utils(keymgr_virtual_sequencer)


  `uvm_component_new
  push_pull_sequencer#(.DeviceDataWidth(EDN_DATA_SIZE)) edn_pull_sequencer_h;

endclass
