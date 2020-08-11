// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_uart_tx_rx_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_uart_tx_rx_vseq)

  `uvm_object_new

  localparam UART_RX_FIFO_SIZE = 32;

  // A set of bytes expected to be received on TX.
  byte exp_uart_tx_data[] = {
    8'he8,
    8'h50,
    8'hc6,
    8'hb4,
    8'hbe,
    8'h16,
    8'hed,
    8'h55,
    8'h16,
    8'h1d,
    8'he6,
    8'h1c,
    8'hde,
    8'h9f,
    8'hfd,
    8'h24,
    8'h89,
    8'h81,
    8'h4d,
    8'h0d,
    8'h1a,
    8'h12,
    8'h4f,
    8'h57,
    8'hea,
    8'hd6,
    8'h6f,
    8'hc0,
    8'h7d,
    8'h46,
    8'he7,
    8'h37,
    8'h81,
    8'hd3,
    8'h8e,
    8'h16,
    8'had,
    8'h7b,
    8'hd0,
    8'he2,
    8'h4f,
    8'hff,
    8'h39,
    8'he6,
    8'h71,
    8'h3c,
    8'h82,
    8'h04,
    8'hec,
    8'h3a,
    8'h27,
    8'hcc,
    8'h3d,
    8'h58,
    8'h0e,
    8'h56,
    8'hd2,
    8'hd2,
    8'hb9,
    8'ha3,
    8'hb5,
    8'h3d,
    8'hc0,
    8'h40,
    8'hba,
    8'h90,
    8'h16,
    8'hd8,
    8'he3,
    8'ha4,
    8'h22,
    8'h74,
    8'h80,
    8'hcb,
    8'h7b,
    8'hde,
    8'hd7,
    8'h3f,
    8'h4d,
    8'h93,
    8'h4d,
    8'h59,
    8'h79,
    8'h88,
    8'h24,
    8'he7,
    8'h68,
    8'h8b,
    8'h7a,
    8'h78,
    8'hb7,
    8'h07,
    8'h09,
    8'h26,
    8'hcf,
    8'h6b,
    8'h52,
    8'hd9,
    8'h4c,
    8'hd3,
    8'h33,
    8'hdf,
    8'h2e,
    8'h0d,
    8'h3b,
    8'hab,
    8'h45,
    8'h85,
    8'hc2,
    8'hc2,
    8'h19,
    8'he5,
    8'hc7,
    8'h2b,
    8'hb0,
    8'hf6,
    8'hcb,
    8'h06,
    8'hf6,
    8'he2,
    8'hf5,
    8'hb1,
    8'hab,
    8'hef,
    8'h6f,
    8'hd8,
    8'h23,
    8'hfd
  };

  // A set of bytes to be send back over RX.
  byte uart_rx_data[] = {
    8'h1b,
    8'h95,
    8'hc5,
    8'hb5,
    8'h8a,
    8'ha4,
    8'ha8,
    8'h9f,
    8'h6a,
    8'h7d,
    8'h6b,
    8'h0c,
    8'hcd,
    8'hd5,
    8'ha6,
    8'h8f,
    8'h07,
    8'h3a,
    8'h9e,
    8'h82,
    8'he6,
    8'ha2,
    8'h2b,
    8'he0,
    8'h0c,
    8'h30,
    8'he8,
    8'h5a,
    8'h05,
    8'h14,
    8'h79,
    8'h8a,
    8'hFf,
    8'h88,
    8'h29,
    8'hda,
    8'hc8,
    8'hdd,
    8'h82,
    8'hd5,
    8'h68,
    8'ha5,
    8'h9d,
    8'h5a,
    8'h48,
    8'h02,
    8'h7f,
    8'h24,
    8'h32,
    8'haf,
    8'h9d,
    8'hca,
    8'ha7,
    8'h06,
    8'h0c,
    8'h96,
    8'h65,
    8'h18,
    8'he4,
    8'h7f,
    8'h26,
    8'h44,
    8'hf3,
    8'h14,
    8'hC1,
    8'he7,
    8'hd9,
    8'h82,
    8'hf7,
    8'h64,
    8'he8,
    8'h68,
    8'hf9,
    8'h6c,
    8'ha9,
    8'he7,
    8'hd1,
    8'h9b,
    8'hac,
    8'he1,
    8'hFd,
    8'hd8,
    8'h59,
    8'hb7,
    8'h8e,
    8'hdc,
    8'h24,
    8'hb8,
    8'ha7,
    8'haf,
    8'h20,
    8'hee,
    8'h6c,
    8'h61,
    8'h48,
    8'h41,
    8'hB4,
    8'h62,
    8'h3c,
    8'hcb,
    8'h2c,
    8'hbb,
    8'he4,
    8'h44,
    8'h97,
    8'h8a,
    8'h5e,
    8'h2f,
    8'h7f,
    8'h2b,
    8'h10,
    8'hcc,
    8'h7d,
    8'h89,
    8'h32,
    8'hfd,
    8'hfd,
    8'h58,
    8'h7f,
    8'hd8,
    8'hc7,
    8'h33,
    8'hd1,
    8'h6a,
    8'hc7,
    8'hba,
    8'h78,
    8'h69
  };

  virtual task body();
    super.body();

    // Spawn off a thread to retrieve UART TX items.
    fork
      get_uart_tx_items();
    join_none

    // Wait until we receive at least 1 byte from the DUT (SW test).
    wait(uart_tx_data_q.size() > 0);

    // Start sending uart_rx_data in over RX.
    fork
      send_uart_rx_data();
    join_none

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
