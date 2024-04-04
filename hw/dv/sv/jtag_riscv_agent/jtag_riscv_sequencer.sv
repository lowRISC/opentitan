// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_riscv_sequencer extends dv_base_sequencer #(
    .ITEM_T (jtag_riscv_item),
    .CFG_T  (jtag_riscv_agent_cfg)
);
  `uvm_component_utils(jtag_riscv_sequencer)

  `uvm_component_new

  // Declare low-level agent sequencer handle in order to reuse its sequence.
  jtag_sequencer jtag_sequencer_h;
endclass
