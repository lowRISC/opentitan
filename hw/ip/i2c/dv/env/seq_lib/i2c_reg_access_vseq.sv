// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_reg_access_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_reg_access_vseq)

  rand uint dly_to_access_reg;
  rand bit  wait_for_idle;

  rand bit [TL_DW-1:0] wr_data;

  constraint num_trans_c {
    num_trans inside {[5:20]};
  }
  constraint dly_to_access_reg_c {
    dly_to_access_reg inside {[1:20]};
  }

  constraint wr_data_c {
    wr_data inside {[0:65535]};
  }
  `uvm_object_new

  //----
  task pre_start();
    super.pre_start();
    num_trans.rand_mode(0);
  endtask

  //----
  task body();
    fork
      wr_rd_compare();
    join
  endtask: body

  // write, read back and check the register values
  task wr_rd_compare();
    bit [TL_DW-1:0] rd_data;
    bit [TL_DW-1:0] exp_data;

    for (int i = 1; i <= num_trans; i++) begin
      // start each new run by randomizing dut parameters
      `DV_CHECK_RANDOMIZE_FATAL(this)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_reg)

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(wr_data)
      exp_data = wr_data;  //32'hCAFE_EFAC
      csr_wr(.csr(ral.timing0), .value(wr_data));
      cfg.clk_rst_vif.wait_clks(1);
      csr_rd(.ptr(ral.timing0), .value(rd_data));
      if (rd_data != exp_data) begin
        `uvm_error(`gfn, $sformatf("timing0, rd_data: 0x%0x, exp_data: 0x%0x, mismatch!", rd_data, exp_data))
      //end else begin
      //  `uvm_info(`gfn, $sformatf("timing0, rd_data: 0x%0x, exp_data: 0x%0x, mismatch!", rd_data, exp_data), UVM_LOW)
      end

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(wr_data)
      csr_wr(.csr(ral.timing1), .value(wr_data));
      exp_data = wr_data;
      csr_rd(.ptr(ral.timing1), .value(rd_data));
      if (rd_data != exp_data) begin
        `uvm_error(`gfn, $sformatf("timing1, rd_data: 0x%0x, exp_data: 0x%0x, mismatch!", rd_data, exp_data))
      end

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(wr_data)
      csr_wr(.csr(ral.timing2), .value(wr_data));
      exp_data = wr_data;
      csr_rd(.ptr(ral.timing2), .value(rd_data));
      if (rd_data != exp_data) begin
        `uvm_error(`gfn, $sformatf("timing2, rd_data: 0x%0x, exp_data: 0x%0x, mismatch!", rd_data, exp_data))
      end

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(wr_data)
      csr_wr(.csr(ral.timing3), .value(wr_data));
      exp_data = wr_data;
      csr_rd(.ptr(ral.timing3), .value(rd_data));
      if (rd_data != exp_data) begin
        `uvm_error(`gfn, $sformatf("timing3, rd_data: 0x%0x, exp_data: 0x%0x, mismatch!", rd_data, exp_data))
      end

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(wr_data)
      csr_wr(.csr(ral.timing4), .value(wr_data));
      exp_data = wr_data;
      csr_rd(.ptr(ral.timing4), .value(rd_data));
      if (rd_data != exp_data) begin
        `uvm_error(`gfn, $sformatf("timing4, rd_data: 0x%0x, exp_data: 0x%0x, mismatch!", rd_data, exp_data))
      end

      // random delay for the next access
      cfg.clk_rst_vif.wait_clks(dly_to_access_reg);
    end
  endtask : wr_rd_compare

  //----
  task post_start();

  endtask : post_start

  // read interrupts and randomly clear interrupts if set
  task process_interrupts();

  endtask : process_interrupts

endclass : i2c_reg_access_vseq
