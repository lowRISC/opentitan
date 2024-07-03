// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//  i2c_fifo_reset_fmt test vseq
//  this sequence fills fmt fifo with random bytes and resets fmt fifo.
//  checks for fifo empty high
class i2c_host_fifo_reset_fmt_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_host_fifo_reset_fmt_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    print_seq_cfg_vars("pre-start");
  endtask : pre_start

  virtual task body();
    bit [7:0] wr_data[$];
    initialization();
    `uvm_info(`gfn, "\n--> start of i2c_host_fifo_reset_fmt_vseq", UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("number of runs is %0d ", num_runs), UVM_HIGH)
    for (int i = 1; i <= num_runs; i++) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_wr_bytes)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(wr_data, wr_data.size == num_wr_bytes;)
      `uvm_info(`gfn, $sformatf("write transaction length is %0d byte", num_wr_bytes), UVM_HIGH)

      for (int j = 1; j <= num_wr_bytes; j++) begin
        i2c_item fmt_item;
        `uvm_create_obj(i2c_item, fmt_item);
        fmt_item.fbyte_c.constraint_mode(0);

        `DV_CHECK_RANDOMIZE_WITH_FATAL(fmt_item,
          fbyte == wr_data[j-1];
          start == 1'b0;
          read  == 1'b0;
          // Randomize so at least one of format bits is non-zero.
          // This ensures we have something at least to push into the fmt_fifo
          $countones({|fbyte, rcont, nakok}) != 0;

          // For the last write byte of last tran., the stop flag must be set
          // For the last write byte of other tran., stop is randomly set/unset -> stop/rstart
          // The stop flag is 0 for all other fmtfifo items.
          if (j == num_wr_bytes) {
            if (i == num_runs) {
              stop == 1'b1;
            }
          } else {
            stop == 1'b0;
          }
        )

        if (j == num_wr_bytes) begin
          `uvm_info(`gfn, $sformatf("This WRITE transfer ended %0s", (fmt_item.stop) ?
              "with STOP, next transaction should begin with START" :
              "without STOP, next transfer should begin with RSTART"), UVM_DEBUG)
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
