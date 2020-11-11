// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test to verify host and device spi data transfers and circular fifo wrapping
// cpol, cpha, host and device data ordering and sram fofo limits are randomized
class spi_device_smoke_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_smoke_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[1:6]};
  }

  virtual task body();
    bit [31:0] host_data;
    bit [31:0] device_data;
    bit [31:0] device_data_exp;
    uint       avail_bytes;

    for (int i = 1; i <= num_trans; i++) begin
      `uvm_info(`gfn, $sformatf("starting sequence %0d/%0d", i, num_trans), UVM_LOW)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      spi_device_init();
      repeat ($urandom_range(1, 200)) begin
        bit [31:0] host_data_exp_q[$];
        `DV_CHECK_STD_RANDOMIZE_FATAL(host_data)
        `DV_CHECK_STD_RANDOMIZE_FATAL(device_data)
        // check if tx sram full and wait for at least a word to become available
        wait_for_tx_avail_bytes(SRAM_WORD_SIZE, SramSpaceAvail, avail_bytes);
        write_device_words_to_send({device_data});
        wait_for_tx_filled_rx_space_bytes(SRAM_WORD_SIZE, avail_bytes);
        spi_host_xfer_word(host_data, device_data_exp);
        // check if rx sram is empty and wait for at least a word to arrive
        wait_for_rx_avail_bytes(SRAM_WORD_SIZE, SramDataAvail, avail_bytes);
        read_host_words_rcvd(1, host_data_exp_q);
        // TODO: move checks to scoreboard
        `DV_CHECK_CASE_EQ(host_data, host_data_exp_q[0])
        `DV_CHECK_CASE_EQ(device_data, device_data_exp)

        check_for_tx_rx_idle();
      end
    end
  endtask : body

endclass : spi_device_smoke_vseq
