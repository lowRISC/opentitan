// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//  i2c_fifo_reset_rx test vseq
//  this sequence waits for rx fifo full and resets rx fifo.
//  checks for fifo empty high and rx lvl is 0
class i2c_host_fifo_reset_rx_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_host_fifo_reset_rx_vseq)
  `uvm_object_new

  // fast write data to fmt_fifo to quickly trigger fmt_watermark interrupt
  constraint fmt_fifo_access_dly_c { fmt_fifo_access_dly == 0;}
  // fast read data from rd_fifo after it is full in order to quickly finish simulation
  constraint rx_fifo_access_dly_c { rx_fifo_access_dly == 0;}
  // write transaction length is more than fmt_fifo depth to fill up fmt_fifo
  constraint num_data_ovf_c {
    num_data_ovf inside {[I2C_FMT_FIFO_DEPTH/4 : I2C_FMT_FIFO_DEPTH/2]};
  }
  constraint num_wr_bytes_c {
    solve num_data_ovf before num_wr_bytes;
    num_wr_bytes == I2C_FMT_FIFO_DEPTH + num_data_ovf;
  }
  // read transaction length is equal to rx_fifo
  constraint num_rd_bytes_c { num_rd_bytes == I2C_RX_FIFO_DEPTH; }

  local bit check_fifo_full = 1'b1;
  bit read;

  virtual task pre_start();
    // hold reading rx_fifo to ensure rx_fifo gets full
    super.pre_start();
    cfg.seq_cfg.en_rx_watermark = 1'b1;
    print_seq_cfg_vars("pre-start");
  endtask : pre_start

  virtual task body();
    initialization(.mode(Host));
    read = 1'b0;
    `uvm_info(`gfn, "\n--> start of i2c_host_fifo_reset_rx_vseq", UVM_DEBUG)
    fork
      begin
        while (!cfg.under_reset && check_fifo_full) process_fifo_full_status();
      end
      begin
        host_send_trans(1, ReadWrite, read);
        check_fifo_full = 1'b0; // gracefully stop process_fifo_full_status
      end
    join
    `uvm_info(`gfn, "\n--> end of i2c_host_fifo_reset_rx_vseq", UVM_DEBUG)
  endtask : body

  task process_fifo_full_status();
    bit fmt_full, rx_full, fmt_empty, rx_empty;
    bit [TL_DW-1:0] status, fmt_lvl, rx_lvl;

    @(posedge cfg.clk_rst_vif.clk);
    csr_rd(.ptr(ral.status), .value(status), .backdoor(1'b1));
    fmt_full  = bit'(get_field_val(ral.status.fmtfull, status));
    fmt_empty = bit'(get_field_val(ral.status.fmtempty, status));
    rx_full   = bit'(get_field_val(ral.status.rxfull, status));
    rx_empty  = bit'(get_field_val(ral.status.rxempty, status));
    csr_rd(.ptr(ral.fifo_status.fmtlvl), .value(fmt_lvl), .backdoor(1'b1));
    csr_rd(.ptr(ral.fifo_status.rxlvl), .value(rx_lvl), .backdoor(1'b1));
    if (!cfg.under_reset) begin
      if (fmt_full)  begin
        `DV_CHECK_EQ(fmt_lvl, I2C_FMT_FIFO_DEPTH);
      end else begin
        `DV_CHECK_LT(fmt_lvl, I2C_FMT_FIFO_DEPTH);
      end
      if (rx_full)   begin
        `DV_CHECK_EQ(rx_lvl, I2C_RX_FIFO_DEPTH);
         reset_rx_fifo();
      end else begin
        `DV_CHECK_LT(rx_lvl, I2C_RX_FIFO_DEPTH);
      end
      if (fmt_empty) `DV_CHECK_EQ(fmt_lvl, 0);
      if (rx_empty)  `DV_CHECK_EQ(rx_lvl, 0);
    end
  endtask : process_fifo_full_status
endclass : i2c_host_fifo_reset_rx_vseq
