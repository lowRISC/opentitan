// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//  i2c_fifo_reset_fmt test vseq
//  this sequence fills fmt fifo with random bytes and resets fmt fifo.
//  checks for fifo empty high
class i2c_host_fifo_reset_fmt_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_host_fifo_reset_fmt_vseq)
  `uvm_object_new

  i2c_item fmt_item;
  bit last_tran;

  virtual task pre_start();
    super.pre_start();
    print_seq_cfg_vars("pre-start");
  endtask : pre_start

  virtual task body();
    bit [7:0] wr_data[$];
    last_tran = 1'b1;
    initialization();
    fmt_item = new("fmt_item");
    `uvm_info(`gfn, "\n--> start of i2c_host_fifo_reset_fmt_vseq", UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("number of runs is %0d ", num_runs), UVM_HIGH)
    for (int i = 1; i <= num_runs; i++) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_wr_bytes)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(wr_data, wr_data.size == num_wr_bytes;)
      `uvm_info(`gfn, $sformatf("write transaction length is %0d byte", num_wr_bytes), UVM_HIGH)
      for (int i = 1; i <= num_wr_bytes; i++) begin
      `uvm_info(`gfn, $sformatf("VISWA loop I %0d byte", i), UVM_HIGH)
        // randomize until at least one of format bits is non-zero to ensure
        // data format will be pushed into fmt_fifo (if not empty)
        do begin
          `DV_CHECK_RANDOMIZE_WITH_FATAL(fmt_item,
            start == 1'b0;
            read  == 1'b0;
          )
          fmt_item.fbyte = wr_data[i-1];
        end while (!fmt_item.nakok && !fmt_item.rcont && !fmt_item.fbyte);

        // last write byte of last tran., stop flag must be set to issue stop bit
        // last write byte of other tran., stop is randomly set/unset to issue stop/rstart bit
        fmt_item.stop = (i != num_wr_bytes) ? 1'b0 : ((last_tran) ? 1'b1 : fmt_item.stop);
        if (i == num_wr_bytes) begin
          `uvm_info(`gfn, $sformatf("\n  transaction WRITE ended %0s", (fmt_item.stop) ?
              "with STOP, next transaction should begin with START" :
              "without STOP, next transaction should begin with RSTART"), UVM_DEBUG)
        end
        program_format_flag(fmt_item, "program_write_data_to_target");
      end // for num wr bytes
      csr_rd_check(.ptr(ral.host_fifo_status.fmtlvl), .compare_value(num_wr_bytes));
      csr_rd_check(.ptr(ral.status.fmtempty), .compare_value(0));
      cfg.clk_rst_vif.wait_clks($urandom_range(100, 2000));
      reset_fmt_fifo();
      csr_rd_check(.ptr(ral.status.fmtempty), .compare_value(1));
    end // for num runs
    `uvm_info(`gfn, "\n--> end of i2c_host_fifo_reset_fmt_vseq", UVM_DEBUG)

  endtask : body
endclass : i2c_host_fifo_reset_fmt_vseq
