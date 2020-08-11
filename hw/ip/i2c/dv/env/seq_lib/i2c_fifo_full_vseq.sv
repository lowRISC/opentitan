// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic fifo_full test vseq
class i2c_fifo_full_vseq extends i2c_sanity_vseq;
  `uvm_object_utils(i2c_fifo_full_vseq)
  `uvm_object_new

  // fast write data to fmt_fifo to quickly trigger fmt_watermark interrupt
  constraint fmt_fifo_access_dly_c {fmt_fifo_access_dly == 0;}

  // fast read data from rd_fifo to quickly finish simulation (increasing sim. performance)
  constraint rx_fifo_access_dly_c {rx_fifo_access_dly == 0;}

  // write transaction length is more than fmt_fifo depth to fill up fmt_fifo
  constraint num_wr_bytes_c {
    solve num_data_ovf before num_wr_bytes;
    num_wr_bytes == I2C_FMT_FIFO_DEPTH + num_data_ovf;
  }

  // read transaction length is equal to rx_fifo
  constraint num_rd_bytes_c {num_rd_bytes == I2C_RX_FIFO_DEPTH;}

  bit check_fifo_full = 1'b1;
  bit fmt_fifo_full = 1'b0;
  bit rx_fifo_full = 1'b0;

  virtual task body();
    // hold reading rx_fifo to ensure rx_fifo gets full
    cfg.en_rx_watermark = 1'b1;

    fork
      begin
        while (check_fifo_full) process_fifo_full_status();
      end
      begin
        super.body();
        check_fifo_full = 1'b0;  // gracefully stop process_fifo_full_status
      end
    join
    // verify fmt_fifo and rx_fifo has been in full status
    `DV_CHECK_EQ({fmt_fifo_full, rx_fifo_full}, 2'b11);
  endtask : body

  task process_fifo_full_status();
    bit [TL_DW-1:0] status;

    csr_rd(.ptr(ral.status), .value(status), .backdoor(1'b1));
    cfg.clk_rst_vif.wait_clks(1);
    fmt_fifo_full |= bit'(get_field_val(ral.status.fmtfull, status));
    rx_fifo_full |= bit'(get_field_val(ral.status.rxfull, status));
  endtask : process_fifo_full_status

endclass : i2c_fifo_full_vseq
