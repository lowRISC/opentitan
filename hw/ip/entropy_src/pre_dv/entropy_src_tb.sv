// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src system verilog unit test bench
//   The intent of this test bench is to get basics running,
//   such as clocks and reset, basic register writes and reads,
//   basic block operation. No configurable BFMs are included
//   in this environment.

module entropy_src_tb;

  import tlul_pkg::*;
  import entropy_src_reg_pkg::*;

  // tests
  bit smoke_test = 0;
  bit interrupt_test = 0;
  bit lfsr_update_test = 0;
  bit basic_entropy_test = 0;
  bit stress_test = 1;

  // options
  bit  msg_rd_data = 0;

  // parameters`
  localparam EsFifoDepth = 32;
  localparam MAX_INTRP_CNT = 25;
  localparam WD_DELAY = 1000*MAX_INTRP_CNT;

  // general signals
  logic      clk;
  logic      rst_n;
  logic      es_entropy_valid_o;
  logic      es_entropy_fifo_err_o;

  // tlul signals
  tlul_pkg::tl_h2d_t tl_i;
  tlul_pkg::tl_d2h_t tl_o;


  // imported register parameters (for reference)

  // Register Address
//  parameter ENTROPY_SRC_INTR_STATE_OFFSET = 6'h 0;
//  parameter ENTROPY_SRC_INTR_ENABLE_OFFSET = 6'h 4;
//  parameter ENTROPY_SRC_INTR_TEST_OFFSET = 6'h 8;
//  parameter ENTROPY_SRC_ES_REGEN_OFFSET = 6'h c;
//  parameter ENTROPY_SRC_ES_CONF_OFFSET = 6'h 10;
//  parameter ENTROPY_SRC_ES_REV_OFFSET = 6'h 14;
//  parameter ENTROPY_SRC_ES_ENTROPY_OFFSET = 6'h 1c;
//  parameter ENTROPY_SRC_ES_CTRL_OFFSET = 6'h 20;
//  parameter ENTROPY_SRC_ES_STATUS_OFFSET = 6'h 24;
//  parameter ENTROPY_SRC_ES_FDEPTHST_OFFSET = 6'h 28;
//  parameter ENTROPY_SRC_ES_THRESH_OFFSET = 6'h 2c;
//  parameter ENTROPY_SRC_ES_RATE_OFFSET = 6'h 30;
//  parameter ENTROPY_SRC_ES_SEED_OFFSET = 6'h 34;

  //---------------------------
  // testbench support
  //---------------------------
  bit        errflag = 0;
  logic [31:0] rd_data = 0;
  logic [31:0] thresh_level = 0;
  logic [31:0] entropy_rate = 0;
  logic [31:0] fifo_depth = 0;
  logic [31:0] intrp_cnt = 0;

  initial
    begin // initial values
      clk = 0;
      rst_n = 0;
      tl_i.a_valid = 0;
      tl_i.a_address = 0;
      tl_i.a_opcode = PutFullData; // write as default
      tl_i.a_param  = 3'h0;
      tl_i.a_size   = 2'h0;
      tl_i.a_source = 8'h0;
      tl_i.a_user  = 0;
      tl_i.a_mask = 0;
      tl_i.a_data = 0;
      tl_i.d_ready =1;
    end

  initial // clock generation
    begin
      clk = 0;
      forever begin
        #4ns clk = !clk;
      end
    end

  initial // reset generation
    begin
      repeat (4) @ (posedge clk);
      rst_n = 1;
    end

  initial // watchdog
    begin
      repeat (WD_DELAY) @ (posedge clk);
      $display("%t %c[1;31mEntropy_Src watchdog triggered -  FAIL!!! %c[0m",$time,27,27);
      $finish;
    end


  task wr_reg(input logic [31:0] addr, logic [31:0] wdata);
     repeat (1) @ (posedge clk); #1ps;
     while (tl_o.a_ready != 1) begin
       repeat (1) @ (posedge clk); #1ps;
     end
     tl_i.a_valid =1;
     tl_i.a_address = addr;
     tl_i.a_opcode = PutFullData; // write = 0
     tl_i.a_param  = 3'h0;
     tl_i.a_size   = 2'h2;
     tl_i.a_source = 8'h0;
     tl_i.a_mask = 4'hf;
     tl_i.a_data = wdata;
     repeat (1) @ (posedge clk); #1ps;
     tl_i.a_valid = 0;
     tl_i.a_address = 0;
     tl_i.a_opcode = PutFullData; // write as default
     tl_i.a_param  = 3'h0;
     tl_i.a_size   = 2'h0;
     tl_i.a_source = 8'h0;
     tl_i.a_mask = 0;
     tl_i.a_data = 0;
     repeat (1) @ (posedge clk); #1ps;
  endtask

  task rd_reg(input logic [31:0] addr, output logic [31:0] rdata);
     repeat (1) @ (posedge clk); #1ps;
     tl_i.d_ready =1;
     while (tl_o.a_ready != 1) begin
       repeat (1) @ (posedge clk); #1ps;
     end
     tl_i.a_valid =1;
     tl_i.a_address = addr;
     tl_i.a_opcode = Get; // read = 4
     tl_i.a_param  = 3'h0;
     tl_i.a_size   = 2'h2;
     tl_i.a_source = 8'h0;
     tl_i.a_mask = 4'hf;
     while (tl_o.d_valid != 1) begin
       repeat (1) @ (posedge clk); #1ps;
     end
     tl_i.a_valid = 0;
     tl_i.d_ready = 1;
     tl_i.a_address = 0;
     tl_i.a_opcode = PutFullData; // write as default
     tl_i.a_param  = 3'h0;
     tl_i.a_size   = 2'h0;
     tl_i.a_source = 8'h0;
     tl_i.a_mask = 0;
     tl_i.a_data = 0;
     rdata = tl_o.d_data;
     if (msg_rd_data) $display("%t rdata = %h",$time,rdata);
     repeat (1) @ (posedge clk); #1ps;
  endtask

  task cmp_reg(input logic [31:0] addr, logic [31:0] cdata, logic [31:0] cmask);
     logic [31:0] rdata;
     rd_reg(addr,rdata);
     if ((rdata & cmask) !== cdata) begin
       $display("%t      reg addr: %h",$time,addr);
       $display("%t  act raw data: %h",$time,rdata);
       $display("%t exp mask data: %h",$time,(rdata & cmask));
       $display("%t      exp data: %h",$time,cdata);
       $display("%t %c[1;31mRead register miscompare!!! %c[0m",$time,27,27);
       $finish;
       // errflag = 1;
     end
  endtask


  task test_end(input bit errflag);
     cmp_reg(ENTROPY_SRC_ES_STATUS_OFFSET,32'h0000_0000,32'hffff_ffff);
     if (errflag == 1) begin
       $display("%t %c[1;31mEntropy_Src Test FAIL!!! %c[0m",$time,27,27);
     end else begin
       $display("%t %c[1;32mEntropy_Src Test PASSED... %c[0m",$time,27,27);
     end
     $finish;
  endtask


  always @ (posedge es_entropy_valid_o) // interrupt handler
    begin
      if (rst_n) begin  // handle reset case
        if (stress_test) begin
          rd_data = 0;
          for (int i=0; i < thresh_level; i=i+1) begin
            rd_reg({26'b0,ENTROPY_SRC_ES_ENTROPY_OFFSET},rd_data);
          end
          repeat (1) @ (posedge clk); #1ps;
          // reset interrupt
          wr_reg({26'b0,ENTROPY_SRC_INTR_STATE_OFFSET},32'h0000_0001);
          if (es_entropy_valid_o !== 0) begin
            $display("%t %c[1;31mInterrupt did not reset FAIL!!! %c[0m",$time,27,27);
            $finish;
          end
          // randomly change entropy_rate
          void'(randomize (entropy_rate) with { entropy_rate inside {[3:30]};});
          $display("%t Interrupt entropy_rate = %h ",$time,entropy_rate);
          wr_reg({26'b0,ENTROPY_SRC_ES_RATE_OFFSET},(entropy_rate)); // rate
          intrp_cnt++;
          $display("%t Interrupt intrp_cnt = %h ",$time,intrp_cnt);
        end
      end
    end

  //-------------------------------------
  // testcases
  //-------------------------------------
  initial begin
    while (rst_n !== 1'b1) begin // avoid initial x case
      repeat (1) @ (posedge clk); #1ps;
    end
    repeat (10) @ (posedge clk); #1ps;
    // Comon register setup
    // -> placeholder
    repeat (20) @ (posedge clk); #1ps;

    //-----------------------------------------------------
    if (smoke_test) begin
      $display("%t Running smoke_test...",$time);
      cmp_reg({26'b0,ENTROPY_SRC_ES_SEED_OFFSET},32'h1234_5678,32'hffff_ffff);
      wr_reg({26'b0,ENTROPY_SRC_ES_SEED_OFFSET},32'habdc_efab); // wr config reg
      cmp_reg({26'b0,ENTROPY_SRC_ES_SEED_OFFSET},32'habdc_efab,32'hffff_ffff);
      cmp_reg({26'b0,ENTROPY_SRC_ES_REV_OFFSET},32'h0001_0201,32'hffff_ffff);
    end
    //-----------------------------------------------------
    if (interrupt_test) begin
      $display("%t Running interrupt_test...",$time);
      wr_reg({26'b0,ENTROPY_SRC_INTR_ENABLE_OFFSET},32'h0000_0003); // enable intrs
      cmp_reg({26'b0,ENTROPY_SRC_INTR_STATE_OFFSET},32'h000000000,32'hffff_ffff);  // check to see that interrupts are off
      // test intrp 0
      wr_reg({26'b0,ENTROPY_SRC_INTR_TEST_OFFSET},32'h0000_0001);
      cmp_reg({26'b0,ENTROPY_SRC_INTR_STATE_OFFSET},32'h000000001,32'hffff_ffff);  // check interrupt state
      wr_reg({26'b0,ENTROPY_SRC_INTR_STATE_OFFSET},32'h0000_0001);
      cmp_reg({26'b0,ENTROPY_SRC_INTR_STATE_OFFSET},32'h000000000,32'hffff_ffff);  // check to see that interrupts are off
      // test intrp 1
      wr_reg({26'b0,ENTROPY_SRC_INTR_TEST_OFFSET},32'h0000_0002);
      cmp_reg({26'b0,ENTROPY_SRC_INTR_STATE_OFFSET},32'h000000002,32'hffff_ffff);  // check interrupt state
      wr_reg({26'b0,ENTROPY_SRC_INTR_STATE_OFFSET},32'h0000_0002);
      cmp_reg({26'b0,ENTROPY_SRC_INTR_STATE_OFFSET},32'h000000000,32'hffff_ffff);  // check to see that interrupts are off
    end
    //-----------------------------------------------------
    if (lfsr_update_test) begin
      $display("%t Running lfsr_update_test...",$time);
      wr_reg({26'b0,ENTROPY_SRC_ES_RATE_OFFSET},32'h0000_0001); // rate
      wr_reg({26'b0,ENTROPY_SRC_ES_THRESH_OFFSET},32'h0000_0001); // thresh level
      wr_reg({26'b0,ENTROPY_SRC_ES_SEED_OFFSET},32'h1111_1111); // seed
      wr_reg({26'b0,ENTROPY_SRC_ES_CONF_OFFSET},32'h0000_0001); // primary enable
      repeat (10) @ (posedge clk);
      wr_reg({26'b0,ENTROPY_SRC_ES_SEED_OFFSET},32'h2222_2222); // change seed, should not write since fifo is not full
      wr_reg({26'b0,ENTROPY_SRC_ES_CTRL_OFFSET},32'h0000_0001); // init bit on
      wr_reg({26'b0,ENTROPY_SRC_ES_CTRL_OFFSET},32'h0000_0000); // init bit off
      repeat (30) @ (posedge clk);
      cmp_reg({26'b0,ENTROPY_SRC_ES_FDEPTHST_OFFSET},32'h000000020,32'hffff_ffff);  // check to see if FIFO is full
      wr_reg({26'b0,ENTROPY_SRC_ES_SEED_OFFSET},32'h3333_3333); // change seed, should write since init bit is on
      wr_reg({26'b0,ENTROPY_SRC_ES_CTRL_OFFSET},32'h0000_0001); // init bit on
      wr_reg({26'b0,ENTROPY_SRC_ES_CTRL_OFFSET},32'h0000_0000); // init bit off
      repeat (10) @ (posedge clk);
      wr_reg({26'b0,ENTROPY_SRC_ES_REGEN_OFFSET},32'h0000_0001); // clear write enable register, make it off
      wr_reg({26'b0,ENTROPY_SRC_ES_SEED_OFFSET},32'h4444_4444); // change seed, should not write since lock seed bit is on
      cmp_reg({26'b0,ENTROPY_SRC_ES_SEED_OFFSET},32'h3333_3333,32'hffff_ffff);  // check to see that seed did not change
      wr_reg({26'b0,ENTROPY_SRC_ES_CTRL_OFFSET},32'h0000_0001); // init bit on
      wr_reg({26'b0,ENTROPY_SRC_ES_CTRL_OFFSET},32'h0000_0000); // init bit off
      repeat (5) @ (posedge clk);
      // set entropy to off
      wr_reg({26'b0,ENTROPY_SRC_ES_RATE_OFFSET},32'h0000_0000); // rate turned off
      // drain the fifo
      for (int i=0; i < 32; i=i+1) begin
        rd_reg({26'b0,ENTROPY_SRC_ES_ENTROPY_OFFSET},rd_data);
      end
      // clear any interrupts
      wr_reg({26'b0,ENTROPY_SRC_INTR_STATE_OFFSET},32'h0000_0003);
    end
    //-----------------------------------------------------
    if (basic_entropy_test) begin
      $display("%t Running basic_entropy_test...",$time);
      thresh_level = 32'h0000_000f;
      wr_reg({26'b0,ENTROPY_SRC_INTR_ENABLE_OFFSET},32'h0000_0003); // enable intrs
      wr_reg({26'b0,ENTROPY_SRC_ES_SEED_OFFSET},32'h2345_3456); // seed
      wr_reg({26'b0,ENTROPY_SRC_ES_RATE_OFFSET},32'h0000_0008); // rate
      wr_reg({26'b0,ENTROPY_SRC_ES_THRESH_OFFSET},thresh_level); // thresh level
      wr_reg({26'b0,ENTROPY_SRC_ES_CONF_OFFSET},32'h0000_0001); // primary enable
      // read out entropy
      rd_data = 0;
      repeat (20) @ (posedge clk);
      while (rd_data < thresh_level) begin
        rd_reg({26'b0,ENTROPY_SRC_ES_FDEPTHST_OFFSET},rd_data);
      end
      // set entropy to super slow
      wr_reg({26'b0,ENTROPY_SRC_ES_RATE_OFFSET},32'h0000_ffff); // rate
      for (int i=0; i < thresh_level; i=i+1) begin
        rd_reg({26'b0,ENTROPY_SRC_ES_ENTROPY_OFFSET},rd_data);
      end
      rd_reg({26'b0,ENTROPY_SRC_ES_FDEPTHST_OFFSET},fifo_depth);
      // drain the rest of the fifo
      for (int i=0; i < fifo_depth; i=i+1) begin
        rd_reg({26'b0,ENTROPY_SRC_ES_ENTROPY_OFFSET},rd_data);
      end
      repeat (10) @ (posedge clk);
    end
    //-----------------------------------------------------
    if (stress_test) begin
      $display("%t Running stress_test...",$time);
      thresh_level = 32'h0000_0008;
      wr_reg({26'b0,ENTROPY_SRC_INTR_ENABLE_OFFSET},32'h0000_0003); // enable intrs
      wr_reg({26'b0,ENTROPY_SRC_ES_SEED_OFFSET},32'h2345_3456); // seed
      wr_reg({26'b0,ENTROPY_SRC_ES_RATE_OFFSET},32'h0000_0006); // rate
      wr_reg({26'b0,ENTROPY_SRC_ES_THRESH_OFFSET},thresh_level); // thresh level
      wr_reg({26'b0,ENTROPY_SRC_ES_CONF_OFFSET},32'h0000_0001); // primary enable
      // wait for interrupts to process
      while (intrp_cnt < MAX_INTRP_CNT) begin
        repeat (20) @ (posedge clk);
      end
    end
    //-----------------------------------------------------
    repeat (10) @ (posedge clk);
    test_end(errflag);
  end


  //-------------------------------------
  // entropy_src instantiation
  //-------------------------------------

  entropy_src #(.EsFifoDepth(EsFifoDepth))
    u_entropy_src
      (
       .clk_i(clk),
       .rst_ni(rst_n),
       .tl_i(tl_i),
       .tl_o(tl_o),
       .es_entropy_valid_o(es_entropy_valid_o),
       .es_entropy_fifo_err_o(es_entropy_fifo_err_o)
       );

endmodule

