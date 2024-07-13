// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic fifo_full test vseq
class i2c_host_fifo_full_vseq extends i2c_rx_tx_vseq;

  `uvm_object_utils(i2c_host_fifo_full_vseq)
  `uvm_object_new

  /////////////////
  // CONSTRAINTS //
  /////////////////

  // fast write data to fmt_fifo to quickly trigger fmt_threshold interrupt
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

  /////////////
  // METHODS //
  /////////////


  virtual task pre_start();
    // hold reading rx_fifo to ensure rx_fifo gets full
    super.pre_start();
    cfg.seq_cfg.en_rx_threshold = 1'b1;
    print_seq_cfg_vars("pre-start");
  endtask : pre_start


  virtual task body();
    bit do_interrupt = 1'b1;
    bit do_check_fifo_status = 1'b1;
    initialization();
    `uvm_info(`gfn, "\n--> start of i2c_host_fifo_full_vseq", UVM_DEBUG)
    fork
      // Every-cycle, check the fifo status signals are consistent with the reported levels.
      begin
        while (!cfg.under_reset && do_check_fifo_status) begin
          @(posedge cfg.clk_rst_vif.clk);
          check_fifo_status(); // Backdoor-read and check all fifo status signals. (0-time)
        end
      end
      // Process CONTROLLER-Mode interrupts while the stimulus is being generated.
      begin
        while (!cfg.under_reset && do_interrupt) process_interrupts();
      end
      // Generate test stimulus transactions
      begin
        host_send_trans(num_trans, .trans_type(WriteOnly));
        do_check_fifo_status = 1'b0; // gracefully stop check_fifo_status() loop
        do_interrupt = 1'b0; // gracefully stop process_interrupts() loop
      end
    join
    `uvm_info(`gfn, "\n--> end of i2c_host_fifo_full_vseq", UVM_DEBUG)
  endtask : body


  // Backdoor-read the DUT-CONTROLLER fifo status registers, and check that the full and empty
  // flags are consistent with the reported levels and the known size of the fifos.
  //
  task check_fifo_status();

    bit fmt_full, rx_full, fmt_empty, rx_empty;
    bit [TL_DW-1:0] status, fmt_lvl, rx_lvl;

    // Backdoor-read all of the CONTROLLER-Mode fifo status registers.
    csr_rd(.ptr(ral.host_fifo_status.fmtlvl), .value(fmt_lvl), .backdoor(1'b1));
    csr_rd(.ptr(ral.host_fifo_status.rxlvl), .value(rx_lvl), .backdoor(1'b1));
    csr_rd(.ptr(ral.status), .value(status), .backdoor(1'b1));
    fmt_full  = bit'(get_field_val(ral.status.fmtfull, status));
    fmt_empty = bit'(get_field_val(ral.status.fmtempty, status));
    rx_full   = bit'(get_field_val(ral.status.rxfull, status));
    rx_empty  = bit'(get_field_val(ral.status.rxempty, status));

    // Check the reported levels and status bits are consistent with the known fifo sizes.
    if (fmt_full)  `DV_CHECK_EQ(fmt_lvl, I2C_FMT_FIFO_DEPTH)
    else           `DV_CHECK_LT(fmt_lvl, I2C_FMT_FIFO_DEPTH)
    if (rx_full)   `DV_CHECK_EQ(rx_lvl,  I2C_RX_FIFO_DEPTH)
    else           `DV_CHECK_LT(rx_lvl,  I2C_RX_FIFO_DEPTH)
    if (fmt_empty) `DV_CHECK_EQ(fmt_lvl, 0)
    if (rx_empty)  `DV_CHECK_EQ(rx_lvl,  0)

  endtask : check_fifo_status


endclass : i2c_host_fifo_full_vseq
