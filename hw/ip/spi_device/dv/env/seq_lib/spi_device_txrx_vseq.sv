// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this is the base random test, extended by most of the other spi device tests
// there are 3 parallel threads in seq body
// 1. process_tx_write
// 2. process_rx_read
// 3. process_spi_transfer
class spi_device_txrx_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_txrx_vseq)
  `uvm_object_new

  // total bytes for tx/rx for each iteration
  rand uint tx_total_bytes;
  rand uint rx_total_bytes;

  // delay
  rand uint tx_delay;
  rand uint rx_delay;
  rand uint spi_delay;

  rand bit  en_dummy_host_xfer;
  rand bit  en_extra_dly;

  // helper rand variable
  rand bit is_same_host_device_sram_words;

  // semaphores to avoid updating fifo ptr when over/underflow is happening. Issue #103
  semaphore tx_ptr_sema, rx_ptr_sema;
  bit       allow_underflow_overflow;

  constraint tx_total_bytes_c {
    tx_total_bytes inside {[SRAM_SIZE : 10 * SRAM_SIZE]};
    tx_total_bytes[1:0] == 0; // word aligned
  }

  constraint rx_total_bytes_c {
    rx_total_bytes == tx_total_bytes;
  }

  constraint tx_delay_c {
    tx_delay dist {
      0              :/ 1,
      [1   : 100]    :/ 3,
      [101 : 10_000] :/ 1
    };
  }

  constraint rx_delay_c {
    rx_delay dist {
      0              :/ 1,
      [1   : 100]    :/ 3,
      [101 : 10_000] :/ 1
    };
  }

  constraint spi_delay_c {
    spi_delay dist {
      0              :/ 1,
      [1   : 100]    :/ 3,
      [101 : 10_000] :/ 1
    };
  }

  constraint num_trans_c {
    num_trans inside {[2:5]};
  }

  constraint en_dummy_host_xfer_c {
    en_dummy_host_xfer dist {
      0 :/ 4,
      1 :/ 1 // 20% enable dummy transfer
    };
  }

  // lower 2 bits are ignored, use word granularity to contrain the sram setting
  constraint sram_addr_c {
    // if limit is 0, it means 1 word
    sram_host_limit_addr[31:2]   < (SRAM_SIZE/SRAM_WORD_SIZE);
    sram_device_limit_addr[31:2] < (SRAM_SIZE/SRAM_WORD_SIZE);

    sram_host_base_addr   <= sram_host_limit_addr;
    sram_device_base_addr <= sram_device_limit_addr;
    // host and device addr space within sram should not overlap
    if (sram_host_limit_addr < sram_device_base_addr) {
      sram_host_limit_addr[31:2] < sram_device_base_addr[31:2];
      sram_device_limit_addr < SRAM_SIZE;
    } else {
      sram_device_limit_addr[31:2] < sram_host_base_addr[31:2];
      sram_host_limit_addr < SRAM_SIZE;
    }
  }

  // size from 25 to SRAM_SIZE/SRAM_WORD_SIZE-25
  // override it if test extreme cases
  constraint sram_size_constraints_c {
    num_host_sram_words   inside {[25:SRAM_SIZE/SRAM_WORD_SIZE]};
    num_device_sram_words inside {[25:SRAM_SIZE/SRAM_WORD_SIZE]};
    is_same_host_device_sram_words == (num_host_sram_words == num_device_sram_words);
    is_same_host_device_sram_words dist {
      1 :/ 2,
      0 :/ 1
    };
  }
  virtual task spi_device_init();
    super.spi_device_init();
    cfg.m_spi_agent_cfg.en_extra_dly_btw_sck  = en_extra_dly;
    cfg.m_spi_agent_cfg.en_extra_dly_btw_word = en_extra_dly;
  endtask

  virtual task body();
    tx_ptr_sema = new(1);
    rx_ptr_sema = new(1);
    for (int i = 1; i <= num_trans; i++) begin
      bit done_tx_write, done_rx_read, done_xfer;
      `uvm_info(`gfn, $sformatf("starting sequence %0d/%0d", i, num_trans), UVM_LOW)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      spi_device_init();
      fork
        begin
          process_tx_write(tx_total_bytes);
          done_tx_write = 1;
        end
        begin
          process_rx_read(rx_total_bytes);
          done_rx_read = 1;
        end
        begin
          while (!done_tx_write || !done_rx_read) process_spi_xfer();
          done_xfer = 1;
        end
        begin // drive dummy host item
          while (!done_xfer && en_dummy_host_xfer) begin
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(tx_delay)
            cfg.clk_rst_vif.wait_clks(tx_delay);
            spi_host_xfer_dummy_item();
          end
        end
      join
      check_for_tx_rx_idle();
    end // for
  endtask : body

  virtual task process_tx_write(uint xfer_bytes);
    uint sram_avail_bytes;
    uint tx_write_bytes;
    while (xfer_bytes > 0) begin
      bit [31:0] device_words_q[$];
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(tx_delay)
      cfg.clk_rst_vif.wait_clks(tx_delay);

      wait_for_tx_avail_bytes(SRAM_WORD_SIZE, SramSpaceAvail, sram_avail_bytes);
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(tx_write_bytes,
                                         tx_write_bytes <= sram_avail_bytes;
                                         tx_write_bytes <= xfer_bytes;
                                         tx_write_bytes[1:0] == 0;
                                         tx_write_bytes dist {
                                             [1:SRAM_WORD_SIZE]    :/ 1,
                                             [SRAM_WORD_SIZE+1:20] :/ 3,
                                             [21:SRAM_SIZE-1]      :/ 1,
                                             SRAM_SIZE             :/ 1};)
      repeat (tx_write_bytes / SRAM_WORD_SIZE) device_words_q.push_back($urandom);
      `uvm_info(`gfn, $sformatf("tx_write_bytes = %0d, sram_avail_bytes = %0d,\
                                xfer_bytes = %0d",
                                tx_write_bytes, sram_avail_bytes, xfer_bytes), UVM_MEDIUM)

      // make sure ptr isn't being updated while fifo underflow is happening
      if (allow_underflow_overflow) tx_ptr_sema.get();
      write_device_words_to_send(device_words_q);

      // when fifo is empty, need to wait until fifo fetch data from sram before release semaphore
      if (allow_underflow_overflow) begin
        // it takes 4 cycles to fetch data to async fifo
        cfg.clk_rst_vif.wait_clks(4);
        tx_ptr_sema.put();
      end

      xfer_bytes -= tx_write_bytes;
    end
    `uvm_info(`gfn, "done process_tx_write", UVM_MEDIUM)
  endtask : process_tx_write

  virtual task process_rx_read(uint xfer_bytes);
    uint sram_avail_bytes;
    uint rx_read_bytes;
    while (xfer_bytes > 0) begin
      bit [31:0] device_words_q[$];
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rx_delay)
      cfg.clk_rst_vif.wait_clks(rx_delay);

      wait_for_rx_avail_bytes(SRAM_WORD_SIZE, SramDataAvail, sram_avail_bytes);
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(rx_read_bytes,
                                         rx_read_bytes <= sram_avail_bytes;
                                         rx_read_bytes <= xfer_bytes;
                                         rx_read_bytes[1:0] == 0;
                                         rx_read_bytes dist {
                                             [1:SRAM_WORD_SIZE]    :/ 1,
                                             [SRAM_WORD_SIZE+1:20] :/ 3,
                                             [21:SRAM_SIZE-1]      :/ 1,
                                             SRAM_SIZE             :/ 1};)
      `uvm_info(`gfn, $sformatf("rx_read_bytes = %0d, sram_avail_bytes = %0d, xfer_bytes =%0d",
                                rx_read_bytes, sram_avail_bytes, xfer_bytes), UVM_MEDIUM)

      // make sure ptr isn't being updated while fifo overflow is happening
      if (allow_underflow_overflow) rx_ptr_sema.get();
      read_host_words_rcvd(rx_read_bytes / SRAM_WORD_SIZE, device_words_q);
      if (allow_underflow_overflow) rx_ptr_sema.put();

      xfer_bytes -= rx_read_bytes;
    end
    `uvm_info(`gfn, "done process_rx_read", UVM_MEDIUM)
  endtask : process_rx_read

  virtual task process_spi_xfer();
    uint sram_avail_bytes;
    uint spi_bytes;
    bit  is_under_over_flow = 0;
    bit [7:0] device_bytes_q[$];

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(spi_delay)
    cfg.clk_rst_vif.wait_clks(spi_delay);

    if (allow_underflow_overflow) is_under_over_flow = $urandom_range(0, 1);
    get_num_xfer_bytes(is_under_over_flow, sram_avail_bytes);
    if (sram_avail_bytes < SRAM_WORD_SIZE) begin
      `uvm_info(`gfn, "no avail byte for process_spi_xfer", UVM_MEDIUM)
      return;
    end

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(spi_bytes,
                                       spi_bytes <= sram_avail_bytes;
                                       spi_bytes[1:0] == 0;
                                       spi_bytes dist {
                                           [1:SRAM_WORD_SIZE]    :/ 1,
                                           [SRAM_WORD_SIZE+1:20] :/ 3,
                                           [21:SRAM_SIZE-1]      :/ 1,
                                           SRAM_SIZE             :/ 1};)

    // avoid ptr is updated while fifo under/overflow is happening
    if (is_under_over_flow) begin
      fork
        tx_ptr_sema.get();
        rx_ptr_sema.get();
      join
    end
    spi_host_xfer_bytes(spi_bytes, device_bytes_q);
    if (is_under_over_flow) begin
      tx_ptr_sema.put();
      rx_ptr_sema.put();
    end
    `uvm_info(`gfn, "done process_spi_xfer", UVM_MEDIUM)
  endtask : process_spi_xfer

  // send dummy item
  virtual task spi_host_xfer_dummy_item();
    spi_host_dummy_seq m_spi_host_seq;
    `uvm_create_on(m_spi_host_seq, p_sequencer.spi_sequencer_h)
    `uvm_send(m_spi_host_seq)
  endtask

endclass : spi_device_txrx_vseq
