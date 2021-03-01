// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_riscv_virtual_sequencer extends cip_base_virtual_sequencer #(
    .ITEM_T (jtag_riscv_item),
    .CFG_T  (jtag_riscv_agent_cfg)
);
  `uvm_component_utils(jtag_riscv_virtual_sequencer)

  `uvm_component_new

  jtag_sequencer#(.DeviceDataWidth(SRAM_DATA_SIZE)) jtag_sequencer_h;
endclass
