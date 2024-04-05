// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_phy_prim_agent_cfg extends dv_base_agent_cfg;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual flash_phy_prim_if vif;

  `uvm_object_utils_begin(flash_phy_prim_agent_cfg)
  `uvm_object_utils_end

  `uvm_object_new
  bit scb_otf_en;
  bit mon_start = 0;
endclass
