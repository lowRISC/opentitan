// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_uart_tx_rx_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_uart_tx_rx_vseq)

  `uvm_object_new

  localparam uint UART_DATASET_SIZE = 128;
  localparam uint UART_RX_FIFO_SIZE = 32;

  // A set of bytes expected to be received on TX.
  rand byte exp_uart_tx_data[];
  constraint exp_uart_tx_data_c {
    exp_uart_tx_data.size() == UART_DATASET_SIZE;
  }

  // A set of bytes to be send back over RX.
  rand byte uart_rx_data[];
  constraint uart_rx_data_c {
    uart_rx_data.size() == UART_DATASET_SIZE;
  }

  virtual task cpu_init();
    super.cpu_init();
    sw_symbol_backdoor_overwrite("uart_tx_data", exp_uart_tx_data);
    sw_symbol_backdoor_overwrite("exp_uart_rx_data", uart_rx_data);
  endtask

  virtual task body();
    super.body();

    // Spawn off a thread to retrieve UART TX items.
    fork get_uart_tx_items(); join_none

    // Wait until we receive at least 1 byte from the DUT (SW test).
    wait(uart_tx_data_q.size() > 0);

    // Start sending uart_rx_data over RX.
    send_uart_rx_data();

    // Wait until we receive all bytes over TX.
    wait(uart_tx_data_q.size() == exp_uart_tx_data.size());

    // Check if we received the right data set over the TX port.
    `uvm_info(`gfn, "Checking the received UART TX data for consistency.", UVM_LOW)
    foreach (uart_tx_data_q[i]) begin
      `DV_CHECK_EQ(uart_tx_data_q[i], exp_uart_tx_data[i])
    end

    // Send UART_RX_FIFO_SIZE+1 random bytes over RX to create an overflow condition.
    send_uart_rx_data(.size(UART_RX_FIFO_SIZE + 1), .random(1'b1));
  endtask

  // Send data over RX.
  virtual task send_uart_rx_data(int size = -1, bit random = 0);
    uart_default_seq send_rx_seq;
    `uvm_create_on(send_rx_seq, p_sequencer.uart_sequencer_h);
    if (size == -1) size = uart_rx_data.size();
    for (int i = 0; i < size; i++) begin
      byte rx_data = random ? $urandom : uart_rx_data[i];
      `DV_CHECK_RANDOMIZE_WITH_FATAL(send_rx_seq, data == rx_data;)
      `uvm_send(send_rx_seq)
    end
  endtask

endclass : chip_sw_uart_tx_rx_vseq
