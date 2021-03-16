// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// directly test all the interrupt one by one
class spi_device_intr_vseq extends spi_device_txrx_vseq;
  `uvm_object_utils(spi_device_intr_vseq)
  `uvm_object_new

  virtual task body();
    spi_device_intr_e spi_dev_intr;
    bit               is_tx_async_fifo_filled;

    for (int i = 1; i <= num_trans; i++) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      spi_device_init();

      // fill tx async fifo to avoid sending out unknown data
      if (!is_tx_async_fifo_filled) begin
        bit [7:0] device_bytes_q[$];
        // fill the fifo and wait until data is ready
        process_tx_write(ASYNC_FIFO_SIZE);
        csr_spinwait(.ptr(ral.async_fifo_level.txlvl), .exp_data(ASYNC_FIFO_SIZE));
        // clean up tx fifo
        spi_host_xfer_bytes(ASYNC_FIFO_SIZE, device_bytes_q);
        // clean up rx fifo
        process_rx_read(ASYNC_FIFO_SIZE);
        // clean interrupts
        csr_wr(.ptr(ral.intr_state), .value('1));
      end

      repeat (NumSpiDevIntr) begin
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(spi_dev_intr,
                                           spi_dev_intr != NumSpiDevIntr;)
        `uvm_info(`gfn, $sformatf("\nTesting %0s", spi_dev_intr.name), UVM_LOW)
        drive_and_check_one_intr(spi_dev_intr);

        csr_wr(.ptr(ral.intr_state), .value('1));
        check_for_tx_rx_idle();
      end
      `uvm_info(`gfn, $sformatf("finished run %0d/%0d", i, num_trans), UVM_LOW)
    end

  endtask : body

  task drive_and_check_one_intr(spi_device_intr_e spi_dev_intr);
    bit [7:0] device_bytes_q[$];
    uint avail_bytes;

    case (spi_dev_intr)
      RxFifoFull, RxFifoOverflow: begin // test fifo full and overflow together
        // just below fifo full
        spi_host_xfer_bytes(sram_host_byte_size - SRAM_WORD_SIZE, device_bytes_q);
        wait_for_rx_avail_bytes(sram_host_byte_size - SRAM_WORD_SIZE, SramDataAvail, avail_bytes);
        check_interrupts(.interrupts(1 << RxFifoFull), .check_set(0));

        // fifo should be full
        spi_host_xfer_bytes(SRAM_WORD_SIZE, device_bytes_q);
        wait_for_rx_avail_bytes(sram_host_byte_size, SramDataAvail, avail_bytes);
        check_interrupts(.interrupts(1 << RxFifoFull), .check_set(1));

        // fill async fifo and check fifo doesn't overflow
        spi_host_xfer_bytes(ASYNC_FIFO_SIZE, device_bytes_q);
        cfg.clk_rst_vif.wait_clks(4); // for interrupt to triggered
        check_interrupts(.interrupts(1 << RxFifoOverflow), .check_set(0));

        // fill 1 word and check fifo overflow
        spi_host_xfer_bytes(SRAM_WORD_SIZE, device_bytes_q);
        check_interrupts(.interrupts(1 << RxFifoOverflow), .check_set(1));
        check_interrupts(.interrupts(1 << RxFifoGeLevel),
                         .check_set(rx_watermark_lvl inside {[1:sram_host_byte_size]}));

        // clean up rx fifo
        process_rx_read(sram_host_byte_size + ASYNC_FIFO_SIZE);
      end
      RxFifoGeLevel: begin
        uint aligned_watermark = (rx_watermark_lvl >> 2) << 2; // remove lsb 2bits
        uint filled_bytes;

        if (rx_watermark_lvl[1:0] > 0) aligned_watermark += SRAM_WORD_SIZE;

        if (rx_watermark_lvl > 0 && aligned_watermark < sram_host_byte_size) begin
          // just below watermark
          if (aligned_watermark - SRAM_WORD_SIZE > 0) begin
            spi_host_xfer_bytes(aligned_watermark - SRAM_WORD_SIZE, device_bytes_q);
            wait_for_rx_avail_bytes(aligned_watermark - SRAM_WORD_SIZE, SramDataAvail, avail_bytes);
            check_interrupts(.interrupts(1 << RxFifoGeLevel), .check_set(0));
          end
          // equal to watermark
          spi_host_xfer_bytes(SRAM_WORD_SIZE, device_bytes_q);
          wait_for_rx_avail_bytes(aligned_watermark, SramDataAvail, avail_bytes);
          check_interrupts(.interrupts(1 << RxFifoGeLevel), .check_set(1));

          // clean interrupts and test it's edge triggered
          filled_bytes = aligned_watermark + SRAM_WORD_SIZE;
          csr_wr(.ptr(ral.intr_state), .value('1));
          spi_host_xfer_bytes(SRAM_WORD_SIZE, device_bytes_q);
          wait_for_rx_avail_bytes(filled_bytes, SramDataAvail, avail_bytes);
          check_interrupts(.interrupts(1 << RxFifoGeLevel), .check_set(0));

          // clean up rx fifo
          process_rx_read(filled_bytes);
        end
      end
      TxFifoLtLevel: begin
        uint aligned_watermark = (tx_watermark_lvl >> 2) << 2; // remove lsb 2bits
        uint filled_bytes;

        if (tx_watermark_lvl[1:0] > 0) aligned_watermark += SRAM_WORD_SIZE;

        if (tx_watermark_lvl == 0 || tx_watermark_lvl > sram_device_byte_size) begin // no intr
          // fill the sram fifo and async fifo, als wait until data is ready
          process_tx_write(sram_device_byte_size + SRAM_WORD_SIZE);
          wait_for_tx_avail_bytes(sram_device_byte_size, SramDataAvail, avail_bytes);

          // clean up tx fifo
          spi_host_xfer_bytes(sram_device_byte_size + SRAM_WORD_SIZE, device_bytes_q);

          // clean up rx fifo
          process_rx_read(dv_utils_pkg::min2(sram_host_byte_size + ASYNC_FIFO_SIZE,
                                             sram_device_byte_size + SRAM_WORD_SIZE));
          // check no interrupt since tx_watermark_lvl is 0 or over the max size
          check_interrupts(.interrupts(1 << TxFifoLtLevel), .check_set(0));
        end else begin
          // fill async fifo, design has 2 words depth, but only update ptr to 2nd word when 1st
          // one is out
          process_tx_write(SRAM_WORD_SIZE);
          csr_spinwait(.ptr(ral.async_fifo_level.txlvl), .exp_data(SRAM_WORD_SIZE));
          // just at watermark
          if (aligned_watermark != 0) process_tx_write(aligned_watermark);
          if (aligned_watermark > ASYNC_FIFO_SIZE) begin
            cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
            check_interrupts(.interrupts(1 << TxFifoLtLevel), .check_set(0));
          end

          // send one word and fifo is less than watermark
          spi_host_xfer_bytes(SRAM_WORD_SIZE, device_bytes_q);
          cfg.clk_rst_vif.wait_clks(4); // for interrupt to triggered
          check_interrupts(.interrupts(1 << TxFifoLtLevel), .check_set(1));

          // clean up tx fifo
          if (aligned_watermark != 0) spi_host_xfer_bytes(aligned_watermark, device_bytes_q);

          // clean up rx fifo
          process_rx_read(dv_utils_pkg::min2(sram_host_byte_size + ASYNC_FIFO_SIZE,
                                             aligned_watermark + SRAM_WORD_SIZE));
        end
      end
      RxFwModeErr: begin
        // TODO, do it later
      end
      TxFifoUnderflow: begin
        // send one word when fifo is empty
        spi_host_xfer_bytes(SRAM_WORD_SIZE, device_bytes_q);
        cfg.clk_rst_vif.wait_clks(4); // for interrupt to triggered
        check_interrupts(.interrupts(1 << TxFifoUnderflow), .check_set(1));

        // clean up rx fifo
        process_rx_read(SRAM_WORD_SIZE);
      end
    endcase
  endtask : drive_and_check_one_intr
endclass : spi_device_intr_vseq
