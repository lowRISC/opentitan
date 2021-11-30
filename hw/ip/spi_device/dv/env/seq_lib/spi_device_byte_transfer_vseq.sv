// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Byte Access test to verify proper byte data transfer without timeout expiring
class spi_device_byte_transfer_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_byte_transfer_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans == 20;
  }

  virtual task body();
    bit [31:0] host_data;
    bit [31:0] device_data;
    bit [7:0] device_data_exp[$];
    uint       avail_bytes;
    uint       avail_data;

    spi_device_init();
    ral.cfg.timer_v.set(8'hFF);
    csr_update(.csr(ral.cfg));

    for (int i = 1; i <= num_trans; i++) begin
      `uvm_info(`gfn, $sformatf("starting sequence %0d/%0d", i, num_trans), UVM_LOW)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      repeat ($urandom_range(2, 10)) begin
        bit [31:0] host_data_exp_q[$];
        `DV_CHECK_STD_RANDOMIZE_FATAL(host_data)
        `DV_CHECK_STD_RANDOMIZE_FATAL(device_data)
        // check if tx sram full and wait for at least a word to become available
        wait_for_tx_avail_bytes(SRAM_WORD_SIZE, SramSpaceAvail, avail_bytes);
        write_device_words_to_send({device_data});
        wait_for_tx_filled_rx_space_bytes(SRAM_WORD_SIZE, avail_bytes);
        spi_host_xfer_byte(host_data[7:0], device_data_exp[0]);
        read_rx_avail_bytes(SramDataAvail, avail_data);
        `DV_CHECK_CASE_EQ(avail_data, 0)
        spi_host_xfer_byte(host_data[15:8], device_data_exp[1]);
        spi_host_xfer_byte(host_data[23:16], device_data_exp[2]);
        spi_host_xfer_byte(host_data[31:24], device_data_exp[3]);
        // check if rx sram is empty and wait for at least a word to arrive
        wait_for_rx_avail_bytes(SRAM_WORD_SIZE, SramDataAvail, avail_bytes);
        read_host_words_rcvd(1, host_data_exp_q);
        `DV_CHECK_CASE_EQ(host_data, host_data_exp_q[0])
        `DV_CHECK_CASE_EQ(device_data,
            {device_data_exp[3], device_data_exp[2], device_data_exp[1], device_data_exp[0]})
        check_for_tx_rx_idle();
      end
    end
  endtask : body

endclass : spi_device_byte_transfer_vseq
