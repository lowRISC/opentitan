// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_virtual_sequencer extends dv_base_virtual_sequencer #(
    .CFG_T(chip_env_cfg),
    .COV_T(chip_env_cov)
  );
  `uvm_component_utils(chip_virtual_sequencer)

  uart_sequencer  uart_sequencer_h;
  jtag_sequencer  jtag_sequencer_h;
  tl_sequencer    cpu_d_tl_sequencer_h;

  `uvm_component_new

endclass
