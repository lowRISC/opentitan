// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic fifo_full test vseq
class i2c_fifo_full_vseq extends i2c_sanity_vseq;
  `uvm_object_utils(i2c_fifo_full_vseq)
  `uvm_object_new

  // derive this constraint from the i2c_base_vseq instead of i2c_sanity_vseq
  constraint num_trans_c {
    num_trans inside {[cfg.seq_cfg.i2c_min_num_trans : cfg.seq_cfg.i2c_max_num_trans]};
  }

  // fast write data to fmt_fifo to quickly trigger fmt_watermark interrupt
  constraint fmt_fifo_access_dly_c { fmt_fifo_access_dly == 0;}

  // fast read data from rd_fifo to quickly finish simulation (increasing sim. performance)
  constraint rx_fifo_access_dly_c { rx_fifo_access_dly == 0;}

  // write transaction length is more than fmt_fifo depth to fill up fmt_fifo
  constraint num_wr_bytes_c {
    solve num_data_ovf before num_wr_bytes;
    num_wr_bytes == I2C_FMT_FIFO_DEPTH + num_data_ovf;
  }

  // read transaction length is equal to rx_fifo
  constraint num_rd_bytes_c { num_rd_bytes == I2C_RX_FIFO_DEPTH; }

  virtual task body();
    // hold reading rx_fifo to ensure rx_fifo gets full
    cfg.en_rx_watermark = 1'b1;
    `uvm_info(`gfn, "\n--> start i2c_fifo_full_vseq", UVM_DEBUG)
    super.body();
    reset_env_config();
    `uvm_info(`gfn, "\n--> end i2c_fifo_full_vseq", UVM_DEBUG)
  endtask : body

endclass : i2c_fifo_full_vseq
