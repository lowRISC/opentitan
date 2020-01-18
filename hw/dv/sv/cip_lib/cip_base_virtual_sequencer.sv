// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cip_base_virtual_sequencer #(type CFG_T = cip_base_env_cfg,
                                   type COV_T = cip_base_env_cov)
                                   extends dv_base_virtual_sequencer #(CFG_T, COV_T);
  `uvm_component_param_utils(cip_base_virtual_sequencer #(CFG_T, COV_T))

  tl_sequencer        tl_sequencer_h;
  alert_esc_sequencer alert_esc_sequencer_h[string];

  `uvm_component_new

endclass

