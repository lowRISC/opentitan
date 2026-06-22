// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(chip_env_cfg),
    .COV_T(chip_env_cov)
  );
  `uvm_component_utils(chip_virtual_sequencer)

  uart_sequencer       uart_sequencer_hs[NUM_UARTS];
  spi_sequencer        spi_device_sequencer_hs[NUM_SPI_HOSTS];
  i2c_sequencer        i2c_sequencer_hs[NUM_I2CS];
  jtag_riscv_sequencer jtag_sequencer_h;
  spi_sequencer        spi_host_sequencer_h;

  // Grab packets from UART TX port for in-sequence checking.
  uvm_tlm_analysis_fifo #(uart_item) uart_tx_fifos[NUM_UARTS];

  // Grab packets from I2C read FIFOs.
  uvm_tlm_analysis_fifo #(i2c_item) i2c_rd_fifos[NUM_I2CS];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    foreach (uart_tx_fifos[i]) uart_tx_fifos[i] = new($sformatf("uart_tx_fifo%0d", i), this);
    foreach (i2c_rd_fifos[i]) i2c_rd_fifos[i] = new($sformatf("i2c_rd_fifo%0d", i), this);
  endfunction

endclass
