// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_monitor_cfg  extends dv_base_agent_cfg;

  int monitor_id = 0;
  bit en_monitor = 1'b1; // enable monitor
  bit invert     = 1'b0; // 0: active high,  1: active low
  bit active     = 1'b0; // 1: collect items 0: ignore
  int resolution = 0;

  // interface handle
  virtual pwm_if vif;

  `uvm_object_utils_begin(pwm_monitor_cfg)
  `uvm_object_utils_end
  `uvm_object_new

endclass
