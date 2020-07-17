// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic fifo_overflow test vseq
class i2c_fifo_overflow_vseq extends i2c_fifo_watermark_vseq;
  `uvm_object_utils(i2c_fifo_overflow_vseq)

  `uvm_object_new

  // counting the number of received overflow interrupts
  local uint num_fmt_overflow;
  local uint num_rx_overflow;
  rand  uint num_data_rx_ovf;

  // send more one data than rx_fifo depth to trigger rx_overflow
  constraint num_rd_bytes_c {
    num_rd_bytes == I2C_RX_FIFO_DEPTH + 1;
  }

  virtual task body();
    bit check_fmt_overflow;
    bit check_rx_overflow;
    bit rxempty = 1'b0;
    device_init();
    host_init();

    // config fmt_overflow and rx_overflow tests
    cfg.en_fmt_overflow = 1'b1;
    cfg.en_rx_overflow = 1'b1;

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_trans)
    for (int i = 0; i < num_trans; i++) begin
      check_fmt_overflow = 1'b1; // set to gracefully stop check_fmt_overflow_intr
      check_rx_overflow  = 1'b1; // set to gracefully stop check_rx_overflow_intr
      num_fmt_overflow   = 0;
      num_rx_overflow    = 0;

      fork
        begin
          //*** verify fmt_overflow irq:
          // -> send write transaction -> pooling and counting fmt_overflow interrupt
          // -> check write complete -> stop pooling fmt_overflow interrupt
          // -> verify the number of received fmt_watermark interrupt
          // -> verify fmt_data dropped is performed scoreboard
          if (check_fmt_overflow) begin
            host_send_trans(.num_trans(1), .trans_type(WriteOnly));
            csr_spinwait(.ptr(ral.status.fmtempty), .exp_data(1'b1));
            check_fmt_overflow = 1'b0;
            // number of fmt_overflow received is at most num_data_rx_ovf
            // since fmt_fifo can be drained thus decreasing num_fmt_overflow counter
            `DV_CHECK_GT(num_fmt_overflow, 0)
            `DV_CHECK_LE(num_fmt_overflow, num_data_ovf)
            `uvm_info(`gfn, $sformatf("\nRun %0d, num_fmt_overflow %0d",
                i, num_fmt_overflow), UVM_DEBUG)
          end

          //*** verify rx_overflow irq:
          // -> send read transaction -> pooling and counting rx_overflow interrupt
          // -> check write complete -> stop pooling rx_overflow interrupt
          // -> verify the number of received rx_overflow interrupt
          // -> verify the rx_data dropped is performed in scoreboard
          if (check_rx_overflow) begin
            host_send_trans(.num_trans(1), .trans_type(ReadOnly));
            csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b1));
            check_rx_overflow = 1'b0;
            `DV_CHECK_EQ(num_rx_overflow, 1)
            `uvm_info(`gfn, $sformatf("\nRun %0d, num_rx_overflow %d",
                i, num_rx_overflow), UVM_DEBUG)
          end
        end
        begin
          while (check_fmt_overflow) check_fmt_overflow_intr();
        end
        begin
          while (check_rx_overflow) check_rx_overflow_intr();
        end
      join
    end
  endtask : body

  task check_fmt_overflow_intr();
    bit fmt_overflow;

    csr_rd(.ptr(ral.intr_state.fmt_overflow), .value(fmt_overflow));
    if (fmt_overflow) begin
      clear_interrupt(FmtOverflow);
      num_fmt_overflow++;
    end
  endtask : check_fmt_overflow_intr

  task check_rx_overflow_intr();
    bit rx_overflow;

    csr_rd(.ptr(ral.intr_state.rx_overflow), .value(rx_overflow));
    if (rx_overflow) begin
      clear_interrupt(RxOverflow);
      num_rx_overflow++;
    end
  endtask : check_rx_overflow_intr

endclass : i2c_fifo_overflow_vseq
