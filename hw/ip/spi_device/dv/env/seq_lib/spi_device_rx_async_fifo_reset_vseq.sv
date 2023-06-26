// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// RX ASYNC FIFO test with driving data resetting async rx fifo and driving new data
class spi_device_rx_async_fifo_reset_vseq extends spi_device_txrx_vseq;
  `uvm_object_utils(spi_device_rx_async_fifo_reset_vseq)
  `uvm_object_new

  constraint sram_size_constraints_c {
    num_host_sram_words dist {
      1 :/ 1,
      2 :/ 1,
      3 :/ 1,
      4 :/ 1
    };
  }

  virtual task body();
    bit [31:0] host_data;
    bit [31:0] device_data;
    bit [31:0] device_data_exp;
    bit [7:0]  rx_level;
    uint       avail_bytes;
    uint       avail_data;
    bit [31:0] host_data_exp_q[$];

    spi_device_fw_init();
    // Disable prim_flip_2sync destination pulse assertions
    fifo_underflow_overflow_sva_control(0);
    `DV_CHECK_STD_RANDOMIZE_FATAL(host_data)
    `DV_CHECK_STD_RANDOMIZE_FATAL(device_data)
    wait_for_tx_avail_bytes(SRAM_WORD_SIZE, SramSpaceAvail, avail_bytes);
    // Start SPI transfers to fill up the RX SRAM FIFO and at least part of the RX async FIFO
    for (int i = 0; i < 6; i++) begin
      write_device_words_to_send({device_data});
    end
    cfg.clk_rst_vif.wait_clks(16);
    for (int i = 0; i < 6; i++) begin
      spi_host_xfer_word(host_data, device_data_exp);
    end
    csr_rd(.ptr(ral.async_fifo_level.rxlvl), .value(rx_level));
    `DV_CHECK_CASE_NE(rx_level, 0)
    // Program `rst_rxfifo` to reset the async FIFO
    csr_wr(.ptr(ral.control.rst_rxfifo), .value(1));
    cfg.clk_rst_vif.wait_clks(100);
    csr_wr(.ptr(ral.control.rst_rxfifo), .value(0));
    // Check `async_fifo_level.rxlvl` is 0
    csr_rd_check(.ptr(ral.async_fifo_level.rxlvl), .compare_value(0));
    // Write sram_host_base_addr into read and write point of RX SRAM FIFO
    ral.rxf_ptr.wptr.set(sram_host_base_addr);
    ral.rxf_ptr.rptr.set(sram_host_base_addr);
    csr_update(.csr(ral.rxf_ptr));
    // Fill TX SRAM FIFO with some other data and start another SPI transfers
    for (int i = 0; i < 6; i++) begin
      write_device_words_to_send({32'h12345678});
    end
    cfg.clk_rst_vif.wait_clks(16);
    for (int i = 0; i < 6; i++) begin
      spi_host_xfer_word(32'h12345678, device_data_exp);
    end
    // Restore prim_flip_2sync destination pulse assertions
    fifo_underflow_overflow_sva_control(1);

  endtask : body

endclass : spi_device_rx_async_fifo_reset_vseq
