// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_virtual_sequencer extends cip_base_virtual_sequencer #(.CFG_T(uart_env_cfg),
                                                                  .COV_T(uart_env_cov));
  `uvm_component_utils(uart_virtual_sequencer)

  uart_sequencer  uart_sequencer_h;

  `uvm_component_new

endclass
