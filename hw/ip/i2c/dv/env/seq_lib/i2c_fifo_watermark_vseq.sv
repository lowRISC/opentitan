// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test the watermark interrupt of fmt_fifo and rx_fifo
class i2c_fifo_watermark_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_fifo_watermark_vseq)

  `uvm_object_new

  // counting the number of received watermark interrupts
  local uint num_fmt_watermark;
  local uint num_rx_watermark;

  // the number of re-programming fmtilvl and rxilvl
  local rand uint num_reprog_ilvl;
  constraint num_reprog_ilvl_c { num_reprog_ilvl inside {[8 : 16]}; }

  // fast write data to fmt_fifo to quickly trigger fmt_watermark interrupt
  constraint fmt_fifo_access_dly_c { fmt_fifo_access_dly == 0;}

  // fast read data from rd_fifo to quickly finish simulation (increasing sim. performance)
  constraint rx_fifo_access_dly_c { rx_fifo_access_dly == 0;}

  // per each run, send a single read/write transaction
  constraint num_trans_c { num_trans == 1; }

  // transaction length is long enough (not less than fmt/rx_fifo depth)
  // in order to cross the watermark levels of rx_fifo and fmt_fifo
  constraint num_wr_bytes_c { num_wr_bytes == I2C_FMT_FIFO_DEPTH + 5; }
  constraint num_rd_bytes_c { num_rd_bytes == I2C_RX_FIFO_DEPTH; }

  task body();
    bit check_fmt_watermark, check_rx_watermark;

    device_init();
    host_init();

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_reprog_ilvl)
    for (int i = 0; i < num_reprog_ilvl; i++) begin
      check_fmt_watermark = 1'b1;
      check_rx_watermark  = 1'b1;
      num_fmt_watermark   = 0;
      num_rx_watermark    = 0;

      fork
        begin
          // verify fmt_watermark irq:
          // -> send write transaction -> pooling and counting fmt_watermark interrupt
          // -> check write complete -> stop pooling fmt_watermark interrupt
          // -> verify the number of received fmt_watermark interrupt
          if (check_fmt_watermark) begin
            host_send_trans(num_trans, "WriteOnly");
            csr_spinwait(.ptr(ral.status.fmtempty), .exp_data(1'b1));
            check_fmt_watermark = 1'b0;
            // depending the programmed fmtivl, the num_fmt_watermark could be 1 or 2
            `DV_CHECK_GT(num_fmt_watermark, 0)
            `DV_CHECK_LE(num_fmt_watermark, 2)
            `uvm_info(`gfn, $sformatf("\nRun %0d, num_fmt_watermark %0d",
                i, num_fmt_watermark), UVM_LOW)
          end

          // verify rx_watermark irq:
          // -> send read transaction -> pooling and counting rx_watermark interrupt
          // -> check read complete -> stop pooling rx_watermark interrupt
          // -> verify the number of received rx_watermark interrupt
          if (check_rx_watermark) begin
            // unset delay_read_rx_until_full to quickly fill up rx_fifo so
            // watermark interrupt is assuredly triggered
            delay_read_rx_until_full = 1'b0;
            host_send_trans(num_trans, "ReadOnly");
            csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b1));
            check_rx_watermark = 1'b0;
            // for fmtilvl > 4, rx_watermark is disable (num_rx_watermark = 0)
            // otherwise, num_rx_watermark must be 1
            if ( rxilvl <= 4) begin
              `DV_CHECK_EQ(num_rx_watermark, 1)
            end else begin
              `DV_CHECK_EQ(num_rx_watermark, 0)
            end
            // during a read transaction, fmt_watermark could be triggered (e.g. since
            // read address and control byte are programmed to fmt_fifo which might cross fmtilvl)
            // if fmt_watermark is triggered, then clear it to not interfere counting the
            // fmt_watermark interrupt of next transaction (no need to verify fmt_watermark again)
            clear_interrupt(FmtWatermark);
            `uvm_info(`gfn, $sformatf("\nRun %0d, num_fmt_watermark %0d",
                i, num_fmt_watermark), UVM_LOW)
          end
        end
        begin
          while (check_fmt_watermark) check_fmt_watermark_intr();
        end
        begin
          while (check_rx_watermark) check_rx_watermark_intr();
        end
      join
    end
  endtask : body

  task check_fmt_watermark_intr();
    bit [TL_DW-1:0] intr_state;
    bit fmt_watermark;

    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    fmt_watermark = bit'(get_field_val(ral.intr_state.fmt_watermark, intr_state));
    if (fmt_watermark) begin
      clear_interrupt(FmtWatermark);
      num_fmt_watermark++;
    end
  endtask : check_fmt_watermark_intr

  task check_rx_watermark_intr();
    bit [TL_DW-1:0] intr_state;
    bit rx_watermark;

    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    rx_watermark = bit'(get_field_val(ral.intr_state.rx_watermark, intr_state));
    if (rx_watermark) begin
      clear_interrupt(RxWatermark);
      num_rx_watermark++;
    end
  endtask : check_rx_watermark_intr

endclass : i2c_fifo_watermark_vseq
