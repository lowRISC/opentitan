// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_handler_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(alert_handler_env_cfg),
    .COV_T(alert_handler_env_cov)
  );
  alert_esc_sequencer alert_host_seqr_h[];
  alert_esc_sequencer esc_device_seqr_h[];

  `uvm_component_utils(alert_handler_virtual_sequencer)

  `uvm_component_new

endclass
