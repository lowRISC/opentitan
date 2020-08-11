// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test the watermark interrupt of fmt_fifo and rx_fifo
class i2c_fifo_watermark_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_fifo_watermark_vseq)

  `uvm_object_new

  // counting the number of received watermark interrupts
  local uint cnt_fmt_watermark;
  local uint cnt_rx_watermark;

  // fast write data to fmt_fifo to quickly trigger fmt_watermark interrupt
  constraint fmt_fifo_access_dly_c {fmt_fifo_access_dly == 0;}

  // fast read data from rd_fifo to quickly finish simulation (increasing sim. performance)
  constraint rx_fifo_access_dly_c {rx_fifo_access_dly == 0;}

  // write transaction length is more than fmt_fifo depth to cross fmtilvl
  constraint num_wr_bytes_c {
    solve num_data_ovf before num_wr_bytes;
    num_wr_bytes == I2C_FMT_FIFO_DEPTH + num_data_ovf;
  }
  // read transaction length is equal to rx_fifo depth to cross rxilvl
  constraint num_rd_bytes_c {num_rd_bytes == I2C_RX_FIFO_DEPTH;}

  virtual task body();
    bit check_fmt_watermark, check_rx_watermark;

    device_init();
    host_init();

    // config rx_watermark test (fmt_watermark test is auto configed)
    cfg.en_rx_watermark = 1'b1;

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_trans)
    for (int i = 0; i < num_trans; i++) begin
      check_fmt_watermark = 1'b1;
      check_rx_watermark = 1'b1;
      cnt_fmt_watermark = 0;
      cnt_rx_watermark = 0;

      fork
        begin
          //*** verify fmt_watermark irq:
          // -> send write transaction -> pooling and counting fmt_watermark interrupt
          // -> check write complete -> stop pooling fmt_watermark interrupt
          // -> verify the number of received fmt_watermark interrupt
          if (check_fmt_watermark) begin
            host_send_trans(.num_trans(1), .trans_type(WriteOnly));
            csr_spinwait(.ptr(ral.status.fmtempty), .exp_data(1'b1));
            check_fmt_watermark = 1'b0;  // gracefully stop process_fmt_watermark_intr
            // depending the programmed fmtivl and the DUT configuration
            // (timing regsisters), cnt_fmt_watermark could be
            //   1: fmtilvl is crossed one   when data drains from fmt_fifo
            //   2: fmtilvl is crossed twice when data fills up or drains from fmt_fifo
            `DV_CHECK_GT(cnt_fmt_watermark, 0)
            `DV_CHECK_LE(cnt_fmt_watermark, 2)
            `uvm_info(`gfn, $sformatf("\nrun %0d, cnt_fmt_watermark %0d", i, cnt_fmt_watermark),
                      UVM_DEBUG)
          end

          //*** verify rx_watermark irq:
          // -> send read transaction -> pooling and counting rx_watermark interrupt
          // -> check read complete -> stop pooling rx_watermark interrupt
          // -> verify the number of received rx_watermark interrupt
          if (check_rx_watermark) begin
            // first en_rx_watermark is unset to quickly fill up rx_fifo and
            // watermark interrupt is assuredly triggered
            // until rx_fifo becomes full, en_rx_watermark is set to start reading rx_fifo
            host_send_trans(.num_trans(1), .trans_type(ReadOnly));
            csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b1));
            check_rx_watermark = 1'b0;  // gracefully stop process_rx_watermark_intr
            // for fmtilvl > 4, rx_watermark is disable (cnt_rx_watermark = 0)
            // otherwise, cnt_rx_watermark must be 1
            if (rxilvl <= 4) begin
              `DV_CHECK_EQ(cnt_rx_watermark, 1)
            end else begin
              `DV_CHECK_EQ(cnt_rx_watermark, 0)
            end
            // during a read transaction, fmt_watermark could be triggered since read address
            // and control byte are programmed to fmt_fifo and possibly cross fmtilvl
            // if fmt_watermark is triggered, then it should be cleared to not interfere
            // counting fmt_watermark in the next transaction (no need to verify
            // fmt_watermark again during read)
            clear_interrupt(FmtWatermark);
          end
        end
        begin
          while (check_fmt_watermark) process_fmt_watermark_intr();
        end
        begin
          while (check_rx_watermark) process_rx_watermark_intr();
        end
      join
    end
  endtask : body

  task process_fmt_watermark_intr();
    bit fmt_watermark;

    csr_rd(.ptr(ral.intr_state.fmt_watermark), .value(fmt_watermark));
    if (fmt_watermark) begin
      clear_interrupt(FmtWatermark);
      cnt_fmt_watermark++;
    end
  endtask : process_fmt_watermark_intr

  task process_rx_watermark_intr();
    bit rx_watermark;

    csr_rd(.ptr(ral.intr_state.rx_watermark), .value(rx_watermark));
    if (rx_watermark) begin
      clear_interrupt(RxWatermark);
      cnt_rx_watermark++;
    end
  endtask : process_rx_watermark_intr

endclass : i2c_fifo_watermark_vseq

