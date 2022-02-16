// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class key_sideload_agent_cfg #(
    parameter type KEY_T = keymgr_pkg::hw_key_req_t
) extends dv_base_agent_cfg;


  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual key_sideload_if#(.KEY_T(KEY_T)) vif;

  bit start_default_seq = 1;

  `uvm_object_utils_begin(key_sideload_agent_cfg#(.KEY_T(KEY_T)))
  `uvm_object_utils_end

  `uvm_object_new

endclass
