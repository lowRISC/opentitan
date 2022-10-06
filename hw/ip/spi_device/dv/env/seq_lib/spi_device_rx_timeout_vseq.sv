// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Byte Access test to verify proper byte data transfer with timeout expiring
class spi_device_rx_timeout_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_rx_timeout_vseq)
  `uvm_object_new

  rand bit [7:0] timeout;       // Timeout value to be configured
  rand bit [2:0] timeout_place; // Dictates bytes after which timeout will take place

  constraint timeout_c {
    timeout >= 100;
  }

  constraint num_trans_c {
    num_trans == 20;
  }

  virtual task transfer_check_byte(bit [1:0] byte_n, bit [7:0] tout,
    bit [2:0] tout_place, bit [7:0] host_b, ref bit [7:0] device_d);
    uint available_data;
    bit [7:0] transfer_byte;
    spi_host_xfer_byte(host_b, device_d);
    if (tout_place == 3'd0 && byte_n < 3) begin
      read_rx_avail_bytes(SramDataAvail, available_data);
      `DV_CHECK_CASE_EQ(available_data, 0)
    end
    if (tout_place[byte_n] == 1'b1) begin
      cfg.clk_rst_vif.wait_clks(tout + 10);
      read_rx_avail_bytes(SramDataAvail, available_data);
      `DV_CHECK_CASE_EQ(available_data, byte_n + 1)
    end
  endtask

  virtual task body();
    bit [31:0] host_data;
    bit [31:0] device_data;
    bit [7:0] device_data_exp[$];
    bit [7:0] device_byte;
    uint       avail_bytes;
    uint       avail_data;

    spi_device_fw_init();

    for (int i = 1; i <= num_trans; i++) begin
      `uvm_info(`gfn, $sformatf("starting sequence %0d/%0d", i, num_trans), UVM_LOW)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      ral.cfg.timer_v.set(timeout);
      csr_update(.csr(ral.cfg));
      repeat ($urandom_range(2, 10)) begin
        bit [31:0] host_data_exp_q[$];
        `DV_CHECK_STD_RANDOMIZE_FATAL(host_data)
        `DV_CHECK_STD_RANDOMIZE_FATAL(device_data)
        // check if tx sram full and wait for at least a word to become available
        wait_for_tx_avail_bytes(SRAM_WORD_SIZE, SramSpaceAvail, avail_bytes);
        write_device_words_to_send({device_data});
        wait_for_tx_filled_rx_space_bytes(SRAM_WORD_SIZE, avail_bytes);
        for (int i = 0; i <= 3; i++) begin
          transfer_check_byte(i, timeout, timeout_place, host_data[i * 8 + 7 -: 8], device_byte);
          device_data_exp[i] = device_byte;
        end
        cfg.clk_rst_vif.wait_clks(10);
        read_rx_avail_bytes(SramDataAvail, avail_data);
        `DV_CHECK_CASE_EQ(avail_data, 4)
        read_host_words_rcvd(1, host_data_exp_q);
        `DV_CHECK_CASE_EQ(host_data, host_data_exp_q[0])
        `DV_CHECK_CASE_EQ(device_data,
            {device_data_exp[3], device_data_exp[2], device_data_exp[1], device_data_exp[0]})
        check_for_tx_rx_idle();
      end
    end
  endtask : body

endclass : spi_device_rx_timeout_vseq
