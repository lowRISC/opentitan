// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test tx sram fifo underflow and rx sram fifo overflow by overriding
// read_tx_filled_rx_space_bytes to send spi transfer when there is no space no data available
class spi_device_fifo_underflow_overflow_vseq extends spi_device_txrx_vseq;
  `uvm_object_utils(spi_device_fifo_underflow_overflow_vseq)
  `uvm_object_new

  virtual task body();
    allow_underflow_overflow = 1;
    // when underflow, miso may be unknown, disable checking it
    cfg.m_spi_agent_cfg.en_monitor_checks = 0;
    super.body();
    cfg.m_spi_agent_cfg.en_monitor_checks = 1;
  endtask

  // there may be some data left due to under/overflow, need to flush out all data
  virtual task check_for_tx_rx_idle();
    uint tx_avail_bytes, rx_avail_bytes;
    logic [31:0] device_words_q[$];

    // flush out all remaining tx data in fifo due to overflow
    while (1) begin
      read_tx_avail_bytes(SramDataAvail, tx_avail_bytes);
      if (tx_avail_bytes == 0) break;
      process_spi_xfer();
    end
    // there are some underflow data in fifo, clean them up
    // repeat twice in case some data in async_fifo when sram fifo is full
    repeat (2) begin
      read_rx_avail_bytes(SramDataAvail, rx_avail_bytes);
      if (rx_avail_bytes == 0) break;
      read_host_words_rcvd(rx_avail_bytes / SRAM_WORD_SIZE, device_words_q);
      // if sram fifo was full, data in async fifo will transfer to sram after sram fifo ptr
      // is updated. Wait until data transfer is done
      if (rx_avail_bytes == `get_rx_allocated_sram_size_bytes) begin
        csr_spinwait(.ptr(ral.async_fifo_level.rxlvl), .exp_data(0));
        cfg.clk_rst_vif.wait_clks(2); // 2 cycle for fifo ptr to be updated
      end
    end

    super.check_for_tx_rx_idle();
  endtask

endclass : spi_device_fifo_underflow_overflow_vseq
