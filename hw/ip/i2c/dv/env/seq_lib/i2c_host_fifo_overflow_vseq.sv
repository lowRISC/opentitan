// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic fifo_overflow test vseq
class i2c_host_fifo_overflow_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_host_fifo_overflow_vseq)
  `uvm_object_new

  // fast write data to fmt_fifo to quickly trigger fmt_watermark interrupt
  constraint fmt_fifo_access_dly_c { fmt_fifo_access_dly == 0;}

  // fast read data from rd_fifo to quickly finish simulation (increasing sim. performance)
  constraint rx_fifo_access_dly_c { rx_fifo_access_dly == 0;}

  // write transaction length is more than fmt_fifo depth to cross fmt_thresh
  constraint num_wr_bytes_c {
    solve num_data_ovf before num_wr_bytes;
    num_wr_bytes == I2C_FMT_FIFO_DEPTH + num_data_ovf;
  }

  // send more one data than rx_fifo depth to trigger rx_overflow
  constraint num_rd_bytes_c { num_rd_bytes == I2C_RX_FIFO_DEPTH + 1; }

  // counting the number of received overflow interrupts
  local uint cnt_rx_overflow;

  virtual task pre_start();
    super.pre_start();
    // config rx_overflow test
    cfg.seq_cfg.en_rx_overflow  = 1'b1;
    print_seq_cfg_vars("pre-start");
  endtask : pre_start

  virtual task body();
    bit check_rx_overflow;
    bit rxempty = 1'b0;

    initialization();
    `uvm_info(`gfn, "\n--> start of i2c_host_fifo_overflow_vseq", UVM_DEBUG)
    for (int i = 1; i <= num_trans; i++) begin
      check_rx_overflow  = 1'b1; // set to gracefully stop process_rx_overflow_intr
      cnt_rx_overflow    = 0;

      `uvm_info(`gfn, $sformatf("\n  run simulation %0d/%0d", i, num_trans), UVM_DEBUG)
      fork
        begin
          //*** verify rx_overflow irq:
          // -> send read transaction -> pooling and counting rx_overflow interrupt
          // -> check write complete -> stop pooling rx_overflow interrupt
          // -> verify the number of received rx_overflow interrupt
          // -> verify the rx_data dropped is performed in scoreboard
          if (check_rx_overflow) begin
            host_send_trans(.max_trans(1), .trans_type(ReadOnly));
            check_rx_overflow = 1'b0;
            if (!cfg.under_reset) begin
              `DV_CHECK_EQ(cnt_rx_overflow, 1)
              `uvm_info(`gfn, $sformatf("\n  cnt_rx_overflow %d", cnt_rx_overflow), UVM_DEBUG)
            end
          end
        end
        begin
          while (!cfg.under_reset && check_rx_overflow) process_rx_overflow_intr();
        end
      join
    end
    `uvm_info(`gfn, "\n--> end of i2c_fifo_full_vseq", UVM_DEBUG)
  endtask : body

  task process_rx_overflow_intr();
    bit rx_overflow;

    csr_rd(.ptr(ral.intr_state.rx_overflow), .value(rx_overflow), .backdoor(1'b1));
    if (rx_overflow) begin
      cnt_rx_overflow++;
      clear_interrupt(RxOverflow);
    end else begin
      cfg.clk_rst_vif.wait_clks(1);
    end
  endtask : process_rx_overflow_intr

endclass : i2c_host_fifo_overflow_vseq
