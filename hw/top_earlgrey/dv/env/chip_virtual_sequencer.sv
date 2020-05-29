// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(chip_env_cfg),
    .COV_T(chip_env_cov)
  );
  `uvm_component_utils(chip_virtual_sequencer)

  uart_sequencer  uart_sequencer_h;
  jtag_sequencer  jtag_sequencer_h;
  spi_sequencer   spi_sequencer_h;

  // Grab packets from UART TX port for in-sequence checking.
  uvm_tlm_analysis_fifo #(uart_item) uart_tx_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    uart_tx_fifo = new("uart_tx_fifo", this);
  endfunction

endclass
