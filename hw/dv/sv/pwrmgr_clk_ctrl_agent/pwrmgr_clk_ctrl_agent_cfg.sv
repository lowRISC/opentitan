// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwrmgr_clk_ctrl_agent_cfg extends dv_base_agent_cfg;

  bit clk_ctrl_en = 1;
  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual pwrmgr_clk_ctrl_if vif;
  virtual clk_rst_if clk_rst_vif;
  virtual clk_rst_if esc_clk_rst_vif;
  virtual clk_rst_if lc_clk_rst_vif;
  `uvm_object_utils_begin(pwrmgr_clk_ctrl_agent_cfg)
  `uvm_object_utils_end

  `uvm_object_new

endclass
