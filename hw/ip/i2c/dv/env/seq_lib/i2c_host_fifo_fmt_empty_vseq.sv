// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//  i2c_fifo_reset_fmt test vseq
//  this sequence fills fmt fifo with random bytes and resets fmt fifo.
//  checks for fifo empty high
class i2c_host_fifo_fmt_empty_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_host_fifo_fmt_empty_vseq)
  `uvm_object_new

  i2c_item fmt_item;

  virtual task pre_start();
    super.pre_start();
    print_seq_cfg_vars("pre-start");
  endtask : pre_start

  virtual task body();
     bit do_interrupt;
    initialization();
    `uvm_info(`gfn, "\n--> start of sequence", UVM_DEBUG)
    fork
      begin
        while (!cfg.under_reset && do_interrupt) process_interrupts();
      end
      begin
        for (uint i = 1; i <= num_trans; i++) begin
          do_interrupt = 1'b1;
          host_send_trans(.max_trans(1), .trans_type(WriteOnly), .read(0), .stopbyte(1));
          do_interrupt = 1'b0; // gracefully stop process_interrupts
          csr_rd_check(.ptr(ral.status.fmtempty), .compare_value(1));
          `DV_CHECK_EQ(cfg.lastbyte, 8'hee)
          cfg.lastbyte = 8'h00;
        end
      end
    join
    `uvm_info(`gfn, "\n--> end of sequence", UVM_DEBUG)
  endtask : body

endclass : i2c_host_fifo_fmt_empty_vseq
