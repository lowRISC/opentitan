// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_spi_device_tx_rx_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_spi_device_tx_rx_vseq)

  `uvm_object_new

  localparam uint SPI_DEVICE_DATA_SIZE    = 128;
  localparam uint SPI_DEVICE_RX_SRAM_SIZE = 1024;

  // A set of bytes to be send from SPI_HOST to SPI_DEVICE RX FIFO.
  rand bit [7:0] spi_device_rx_data[];
  constraint spi_device_rx_data_c {
    spi_device_rx_data.size() == SPI_DEVICE_DATA_SIZE;
  }

  // A set of bytes expected to be received on SPI_HOST from SPI_DEVICE TX FIFO.
  rand bit [7:0] exp_spi_device_tx_data[];
  constraint exp_spi_device_tx_data_c {
    exp_spi_device_tx_data.size() == SPI_DEVICE_DATA_SIZE;
  }

  virtual task sync_with_sw();
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
  endtask:sync_with_sw

  virtual task cpu_init();
    super.cpu_init();
    sw_symbol_backdoor_overwrite("spi_device_tx_data", exp_spi_device_tx_data);
    sw_symbol_backdoor_overwrite("exp_spi_device_rx_data", spi_device_rx_data);
  endtask

  virtual task body();
    bit [7:0] spi_device_tx_data[$];
    super.body();

    // Wait SPI_DEVICE filled TX FIFO, otherwise SDO will be X
    sync_with_sw();
    csr_spinwait(.ptr(ral.spi_device.status.txf_full), .exp_data('b1), .backdoor(1),
                 .spinwait_delay_ns(1));

    // Send SPI_HOST data to SPI_DEVICE RX_FIFO and get tx_data from SPI_DEVICE TX_FIFO
    // Check if received tx_data against expected value
    send_spi_host_rx_data(spi_device_tx_data, SPI_DEVICE_DATA_SIZE);
    foreach (spi_device_tx_data[i]) begin
      `DV_CHECK_CASE_EQ(spi_device_tx_data[i], exp_spi_device_tx_data[i])
    end

    // Wait for the CPU to read out the RX_FIFO
    sync_with_sw();

    // Send data to fill RX_SRAM to test RX SRAM FIFO full interrupt
    send_spi_host_rx_data(spi_device_tx_data, SPI_DEVICE_RX_SRAM_SIZE);

    // Wait for RX_FULL interrupt to fire
     sync_with_sw();

    // Send an extra data to test RX Async FIFO overflow
    send_spi_host_rx_data(spi_device_tx_data, SPI_DEVICE_DATA_SIZE);
  endtask

  virtual task send_spi_host_rx_data(ref bit [7:0] device_data[$],input int size);
    spi_host_seq m_spi_host_seq;
    `uvm_create_on(m_spi_host_seq, p_sequencer.spi_host_sequencer_h)
    if (size == SPI_DEVICE_DATA_SIZE) begin
      `DV_CHECK_RANDOMIZE_WITH_FATAL(m_spi_host_seq,
                                     data.size() == size;
                                     foreach (data[i]) {data[i] == spi_device_rx_data[i];})
    end else begin
      `DV_CHECK_RANDOMIZE_WITH_FATAL(m_spi_host_seq, data.size() == size;)
    end
    `uvm_send(m_spi_host_seq)
    device_data = m_spi_host_seq.rsp.data;
  endtask

endclass : chip_sw_spi_device_tx_rx_vseq
