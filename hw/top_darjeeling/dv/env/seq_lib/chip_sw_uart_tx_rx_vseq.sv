// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_uart_tx_rx_vseq extends chip_sw_uart_smoke_vseq;
  `uvm_object_utils(chip_sw_uart_tx_rx_vseq)

  `uvm_object_new

  localparam uint UART_DATASET_SIZE = 128;
  localparam uint UART_RX_FIFO_SIZE = 128;

  // A set of bytes expected to be received on TX.
  rand bit [7:0] exp_uart_tx_data[];
  constraint exp_uart_tx_data_c {
    exp_uart_tx_data.size() == UART_DATASET_SIZE;
  }

  // A set of bytes to be send back over RX.
  rand bit [7:0] uart_rx_data[];
  constraint uart_rx_data_c {
    uart_rx_data.size() == UART_DATASET_SIZE;
  }

  function void pre_randomize();
    uart_idx_smoke_c.constraint_mode(0);
    super.pre_randomize();
  endfunction

  task pre_start();
    void'($value$plusargs("uart_idx=%0d", uart_idx));
    `DV_CHECK_FATAL(uart_idx inside {[0:NUM_UARTS-1]})
    super.pre_start();
  endtask

  virtual task cpu_init();
    // sw_symbol_backdoor_overwrite takes an array as the input
    bit [7:0] uart_idx_data[] = {uart_idx};

    super.cpu_init();
    sw_symbol_backdoor_overwrite("kUartTxData", exp_uart_tx_data);
    sw_symbol_backdoor_overwrite("kExpUartRxData", uart_rx_data);
    sw_symbol_backdoor_overwrite("kUartIdx", uart_idx_data);
  endtask

  virtual task body();
    super.body();

    // Spawn off a thread to retrieve UART TX items.
    fork get_uart_tx_items(uart_idx); join_none

    // Wait until we receive at least 1 byte from the DUT (SW test).
    `DV_WAIT(uart_tx_data_q.size() > 0)

    // Start sending uart_rx_data over RX.
    send_uart_rx_data(.instance_num(uart_idx));

    // Wait until we receive all bytes over TX.
    `DV_WAIT(uart_tx_data_q.size() == exp_uart_tx_data.size())

    // Check if we received the right data set over the TX port.
    `uvm_info(`gfn, "Checking the received UART TX data for consistency.", UVM_LOW)
    foreach (uart_tx_data_q[i]) begin
      `DV_CHECK_EQ(uart_tx_data_q[i], exp_uart_tx_data[i], $sformatf("index: %0d", i))
    end

    // Send UART_RX_FIFO_SIZE+1 random bytes over RX to create an overflow condition.
    send_uart_rx_data(.instance_num(uart_idx), .size(UART_RX_FIFO_SIZE + 1), .random(1'b1));
  endtask

  // Send data over RX.
  virtual task send_uart_rx_data(int instance_num, int size = -1, bit random = 0);
    uart_default_seq send_rx_seq;
    `DV_CHECK_FATAL(instance_num inside {[0:NUM_UARTS-1]})
    `uvm_create_on(send_rx_seq, p_sequencer.uart_sequencer_hs[instance_num]);
    if (size == -1) size = uart_rx_data.size();
    for (int i = 0; i < size; i++) begin
      byte rx_data = random ? $urandom : uart_rx_data[i];
      `DV_CHECK_RANDOMIZE_WITH_FATAL(send_rx_seq, data == rx_data;)
      `uvm_send(send_rx_seq)
    end
  endtask

endclass : chip_sw_uart_tx_rx_vseq
