// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

import tlul_pkg::*;
import trial1_reg_pkg::*;

module trial1_test (
  input                   clk,
  input                   rst_n,

  output tl_h2d_t         tl_h2d,
  input  tl_d2h_t         tl_d2h,

  input  trial1_reg2hw_t  reg2hw,
  output trial1_hw2reg_t  hw2reg
);

  int errorcount = 0;
  logic DEBUG = 1'b1;
  // for now always accept read responses
  assign  tl_h2d.d_ready = 1'b1;

  task automatic send_wr (
    input bit [11:0] waddr,
    input bit [31:0] wdata
  );
    begin
      tl_h2d.a_address <= waddr;
      tl_h2d.a_data <= wdata;
      tl_h2d.a_mask <= 4'hF;
      tl_h2d.a_size <= 'h2;
      tl_h2d.a_opcode <= PutFullData;
      tl_h2d.a_source <= '0;
      tl_h2d.a_param <= '0;
      tl_h2d.a_valid <= 1'b1;
      @(posedge clk);
      while (!tl_d2h.a_ready) @(posedge clk);
      tl_h2d.a_valid <= 1'b0;
      while (!tl_d2h.d_valid) @(posedge clk);
    end
  endtask

  task automatic send_rd (
    input  bit [11:0] raddr,
    output bit [31:0] rdata
  );
    begin
      tl_h2d.a_address  <= raddr;
      tl_h2d.a_opcode <= Get;
      tl_h2d.a_mask <= 4'hF;
      tl_h2d.a_size <= 'h2;
      tl_h2d.a_source <= '0;
      tl_h2d.a_param <= '0;
      tl_h2d.a_valid <= 1'b1;
      @(posedge clk);
      while (!tl_d2h.a_ready) @(posedge clk);
      tl_h2d.a_valid <= 1'b0;
      while (!tl_d2h.d_valid) @(negedge clk);
      rdata = tl_d2h.d_data;
      @(posedge clk);
    end
  endtask

  task automatic test_q (
    string regname,
    input bit [31:0] gotval,
    input bit [31:0] expval
  );
    begin
      if (gotval !== expval) begin
        $error("ERROR: expected q value for %s is %x got %x", regname, expval, gotval);
        errorcount++;
      end else if (DEBUG) begin
        $display("INFO: got expected q value for %s of %x", regname, expval);
      end
    end
  endtask

  // these registers need capturers to see the qe effect

  logic [31:0] rwtype5_capture;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      rwtype5_capture <= 32'h0;
    else if (reg2hw.rwtype5.qe)
      rwtype5_capture <= reg2hw.rwtype5.q;
    end

  logic [31:0] rwtype6_capture;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      rwtype6_capture <= 32'hc8c8c8c8;
    else if (reg2hw.rwtype6.qe)
      rwtype6_capture <= reg2hw.rwtype6.q;
  end
  // externalized register
  assign hw2reg.rwtype6.d = rwtype6_capture;

  logic [31:0] rotype1_capture, my_rotype1_d;
  logic my_rotype1_de;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      rotype1_capture <= 32'h66aa66aa;
    else if (my_rotype1_de)
      rotype1_capture <= my_rotype1_d;
  end
  // externalized register
  assign hw2reg.rotype1.d = rotype1_capture;

  task automatic test_capture (
    string regname,
    input bit [31:0] gotval,
    input bit [31:0] expval
  );
    begin
      if (gotval !== expval) begin
        $error("ERROR: expected hwqe captured value for %s is %x got %x", regname, expval,
                 gotval);
        errorcount++;
      end else if (DEBUG) begin
        $display("INFO: got expected hwqe captured value for %s of %x", regname, expval);
      end
    end
  endtask

  task automatic test_reg (
    string regname,
    input bit [11:0] addr,
    input bit [31:0] expval
  );
    begin
      logic [31:0] gotval;
      send_rd(addr, gotval);
      if (gotval !== expval) begin
        $error("ERROR: expected rd value for %s is %x got %x", regname, expval, gotval);
        errorcount++;
      end else if (DEBUG) begin
        $display("INFO: got expected rd value for %s of %x", regname, expval);
      end
    end
  endtask

  task automatic test_rwtype0(input bit [31:0] expdata);
    // test register read
    test_reg("RWTYPE0", 12'h0, expdata);
    // test q
    test_q("RWTYPE0", reg2hw.rwtype0.q, expdata);
    // holds value
    repeat(5) @(posedge clk);
    // test register read
    test_reg("RWTYPE0", 12'h0, expdata);
    // test q
    test_q("RWTYPE0", reg2hw.rwtype0.q, expdata);
  endtask

  task automatic test_rwtype1(input bit [31:0] expdata);
    logic [31:0] maskexp;
    maskexp = expdata & 32'h0000ff13;
    test_reg("RWTYPE1", 12'h4, maskexp);
    // test q's
    test_q("RWTYPE1.field0", reg2hw.rwtype1.field0.q, maskexp[0]);
    test_q("RWTYPE1.field1", reg2hw.rwtype1.field1.q, maskexp[1]);
    test_q("RWTYPE1.field4", reg2hw.rwtype1.field4.q, maskexp[4]);
    test_q("RWTYPE1.field15_8", reg2hw.rwtype1.field15_8.q, maskexp[15:8]);
    // hold value
    repeat(5) @(posedge clk);
    test_reg("RWTYPE1", 12'h4, maskexp);
    // test q
    test_q("RWTYPE1.field0", reg2hw.rwtype1.field0.q, maskexp[0]);
    test_q("RWTYPE1.field1", reg2hw.rwtype1.field1.q, maskexp[1]);
    test_q("RWTYPE1.field4", reg2hw.rwtype1.field4.q, maskexp[4]);
    test_q("RWTYPE1.field15_8", reg2hw.rwtype1.field15_8.q, maskexp[15:8]);
  endtask

  task automatic test_rwtype2(input bit [31:0] expdata);
    // test register read
    test_reg("RWTYPE2", 12'h8, expdata);
    // test q
    test_q("RWTYPE2", reg2hw.rwtype2.q, expdata);
    // holds value
    repeat(5) @(posedge clk);
    // test register read
    test_reg("RWTYPE2", 12'h8, expdata);
    // test q
    test_q("RWTYPE2", reg2hw.rwtype2.q, expdata);
  endtask

  task automatic test_rwtype3(input bit [31:0] expdata);
    test_reg("RWTYPE3", 12'hc, expdata);
    // test q's
    test_q("RWTYPE3.field0", reg2hw.rwtype3.field0.q, expdata[15:0]);
    test_q("RWTYPE3.field1", reg2hw.rwtype3.field1.q, expdata[31:16]);
    // hold value
    repeat(5) @(posedge clk);
    test_reg("RWTYPE3", 12'hc, expdata);
    // test q
    test_q("RWTYPE3.field0", reg2hw.rwtype3.field0.q, expdata[15:0]);
    test_q("RWTYPE3.field1", reg2hw.rwtype3.field1.q, expdata[31:16]);
  endtask

  task automatic test_rwtype4(input bit [31:0] expdata);
    test_reg("RWTYPE4", 12'h200, expdata);
    // test q's
    test_q("RWTYPE4.field0", reg2hw.rwtype4.field0.q, expdata[15:0]);
    test_q("RWTYPE4.field1", reg2hw.rwtype4.field1.q, expdata[31:16]);
    // hold value
    repeat(5) @(posedge clk);
    test_reg("RWTYPE4", 12'h200, expdata);
    // test q
    test_q("RWTYPE4.field0", reg2hw.rwtype4.field0.q, expdata[15:0]);
    test_q("RWTYPE4.field1", reg2hw.rwtype4.field1.q, expdata[31:16]);
  endtask

  task automatic test_rotype0(input bit [31:0] expdata);
    // test register read
    test_reg("ROTYPE0", 12'h204, expdata);
    // test q
    test_q("ROTYPE0", reg2hw.rotype0.q, expdata);
    // holds value
    repeat(5) @(posedge clk);
    // test register read
    test_reg("ROTYPE0", 12'h204, expdata);
    // test q
    test_q("ROTYPE0", reg2hw.rotype0.q, expdata);
  endtask

  task automatic test_w1ctype0(input bit [31:0] expdata);
    // test register read
    test_reg("W1CTYPE0", 12'h208, expdata);
    // test q
    test_q("W1CTYPE0", reg2hw.w1ctype0.q, expdata);
    // holds value
    repeat(5) @(posedge clk);
    // test register read
    test_reg("W1CTYPE0", 12'h208, expdata);
    // test q
    test_q("W1CTYPE0", reg2hw.w1ctype0.q, expdata);
  endtask

  task automatic test_w1ctype1(input bit [31:0] expdata);
    test_reg("W1CTYPE1", 12'h20c, expdata);
    // test q's
    test_q("W1CTYPE1.field0", reg2hw.w1ctype1.field0.q, expdata[15:0]);
    test_q("W1CTYPE1.field1", reg2hw.w1ctype1.field1.q, expdata[31:16]);
    // hold value
    repeat(5) @(posedge clk);
    test_reg("W1CTYPE1", 12'h20c, expdata);
    // test q
    test_q("W1CTYPE1.field0", reg2hw.w1ctype1.field0.q, expdata[15:0]);
    test_q("W1CTYPE1.field1", reg2hw.w1ctype1.field1.q, expdata[31:16]);
  endtask

  task automatic test_w1ctype2(input bit [31:0] expdata);
    // test register read
    test_reg("W1CTYPE2", 12'h210, expdata);
    // test q
    test_q("W1CTYPE2", reg2hw.w1ctype2.q, expdata);
    // holds value
    repeat(5) @(posedge clk);
    // test register read
    test_reg("W1CTYPE2", 12'h210, expdata);
    // test q
    test_q("W1CTYPE2", reg2hw.w1ctype2.q, expdata);
  endtask

  task automatic test_w1stype2(input bit [31:0] expdata);
    // test register read
    test_reg("W1STYPE2", 12'h214, expdata);
    // test q
    test_q("W1STYPE2", reg2hw.w1stype2.q, expdata);
    // holds value
    repeat(5) @(posedge clk);
    // test register read
    test_reg("W1STYPE2", 12'h214, expdata);
    // test q
    test_q("W1STYPE2", reg2hw.w1stype2.q, expdata);
  endtask

  task automatic test_w0ctype2(input bit [31:0] expdata);
    // test register read
    test_reg("W0CTYPE2", 12'h218, expdata);
    // test q
    test_q("W0CTYPE2", reg2hw.w0ctype2.q, expdata);
    // holds value
    repeat(5) @(posedge clk);
    // test register read
    test_reg("W0CTYPE2", 12'h218, expdata);
    // test q
    test_q("W0CTYPE2", reg2hw.w0ctype2.q, expdata);
  endtask

  task automatic test_r0w1ctype2(input bit [31:0] expdata);
    // test register read
    test_reg("R0W1CTYPE2", 12'h21c, 0);
    // test q
    test_q("R0W1CTYPE2", reg2hw.r0w1ctype2.q, expdata);
    // holds value
    repeat(5) @(posedge clk);
    // test register read
    test_reg("R0W1CTYPE2", 12'h21c, 0);
    // test q
    test_q("R0W1CTYPE2", reg2hw.r0w1ctype2.q, expdata);
  endtask

  task automatic test_rctype0(input bit [31:0] expdata);
    // test q
    test_q("RCTYPE0", reg2hw.rctype0.q, expdata);
    // test register read
    test_reg("RCTYPE0", 12'h220, expdata);
    // second read returns zero value
    repeat(5) @(posedge clk);
    // test register read
    test_reg("RCTYPE0", 12'h220, 32'h0);
    // test q
    test_q("RCTYPE0", reg2hw.rctype0.q, 32'h0);
  endtask

  task automatic test_wotype0(input bit [31:0] expdata);
    // test register read, always returns zero
    test_reg("WOTYPE0", 12'h224, 0);
    // test q
    test_q("WOTYPE0", reg2hw.wotype0.q, expdata);
    // holds value
    repeat(5) @(posedge clk);
    // test register read
    test_reg("WOTYPE0", 12'h224, 32'h0);
    // test q
    test_q("WOTYPE0", reg2hw.wotype0.q, expdata);
  endtask

  task automatic test_mixtype0(input bit [31:0] expdata);
    // test q's
    test_q("MIXTYPE0.field0", reg2hw.mixtype0.field0.q, expdata[3:0]);
    test_q("MIXTYPE0.field1", reg2hw.mixtype0.field1.q, expdata[7:4]);
    test_q("MIXTYPE0.field2", reg2hw.mixtype0.field2.q, expdata[11:8]);
    test_q("MIXTYPE0.field3", reg2hw.mixtype0.field3.q, expdata[15:12]);
    test_q("MIXTYPE0.field4", reg2hw.mixtype0.field4.q, expdata[19:16]);
    test_q("MIXTYPE0.field5", reg2hw.mixtype0.field5.q, expdata[23:20]);
    test_q("MIXTYPE0.field6", reg2hw.mixtype0.field6.q, expdata[27:24]);
    test_q("MIXTYPE0.field7", reg2hw.mixtype0.field7.q, expdata[31:28]);
    // test register
    test_reg("MIXTYPE0", 12'h228, expdata & 32'h0fffffff);  // [31:28] is write-only
    // hold value
    repeat(5) @(posedge clk);
    // [31:28] is write-only, [27:24] is read-clear
    test_reg("MIXTYPE0", 12'h228, expdata & 32'h00ffffff);
    // test q
    test_q("MIXTYPE0.field0", reg2hw.mixtype0.field0.q, expdata[3:0]);
    test_q("MIXTYPE0.field1", reg2hw.mixtype0.field1.q, expdata[7:4]);
    test_q("MIXTYPE0.field2", reg2hw.mixtype0.field2.q, expdata[11:8]);
    test_q("MIXTYPE0.field3", reg2hw.mixtype0.field3.q, expdata[15:12]);
    test_q("MIXTYPE0.field4", reg2hw.mixtype0.field4.q, expdata[19:16]);
    test_q("MIXTYPE0.field5", reg2hw.mixtype0.field5.q, expdata[23:20]);
    test_q("MIXTYPE0.field6", reg2hw.mixtype0.field6.q, 4'h0); // read-clear
    test_q("MIXTYPE0.field7", reg2hw.mixtype0.field7.q, expdata[31:28]);
  endtask

  task automatic test_rwtype5(input bit [31:0] expdata);
    // test register read
    test_reg("RWTYPE5", 12'h22c, expdata);
    // test q
    test_q("RWTYPE5", reg2hw.rwtype5.q, expdata);
    // holds value
    repeat(5) @(posedge clk);
    // test register read
    test_reg("RWTYPE5", 12'h22c, expdata);
    // test q
    test_q("RWTYPE5", reg2hw.rwtype5.q, expdata);
  endtask

  task automatic test_rwtype5_capture(input bit [31:0] expdata);
    // test captured value
    test_capture("RWTYPE5", rwtype5_capture, expdata);
  endtask

  task automatic test_rwtype6(input bit [31:0] expdata);
    // test register read
    test_reg("RWTYPE6", 12'h230, expdata);
    // holds value
    repeat(5) @(posedge clk);
    // test register read
    test_reg("RWTYPE6", 12'h230, expdata);
  endtask

  task automatic test_rwtype6_capture(input bit [31:0] expdata);
    // test captured value
    test_capture("RWTYPE6", rwtype6_capture, expdata);
  endtask

  task automatic test_rwtype7(input bit [31:0] expdata);
    // test register read
    test_reg("RWTYPE7", 12'h23c, expdata);
    // holds value
    repeat(5) @(posedge clk);
    // test register read
    test_reg("RWTYPE7", 12'h23c, expdata);
  endtask

  task automatic test_rotype1(input bit [31:0] expdata);
    // test register read
    test_reg("ROTYPE1", 12'h234, expdata);
    // holds value
    repeat(5) @(posedge clk);
    // test register read
    test_reg("ROTYPE1", 12'h234, expdata);
  endtask

  task automatic test_rotype1_capture(input bit [31:0] expdata);
    // test captured value
    test_capture("ROTYPE1", rotype1_capture, expdata);
  endtask

  task automatic test_rotype2(input bit [31:0] expdata);
    // test register read
    test_reg("ROTYPE2", 12'h238, expdata);
    // holds value
    repeat(5) @(posedge clk);
    // test register read
    test_reg("ROTYPE2", 12'h238, expdata);
  endtask

  // so far just these registers we need to drive back into
  // RWTYPE2[31:0]
  // RWTYPE3.FIELD0[15:0]
  // RWTYPE3.FIELD1[15:0]
  // ROTYPE0[31:0]
  // W1CTYPE2[31:0]
  // W1STYPE2[31:0]
  // W0CTYPE2[31:0]
  // R0W1CTYPE2[31:0]
  // RCTYPE0[31:0]
  // MIXTYPE0.FIELD1[3:0]
  // MIXTYPE0.FIELD3[3:0]
  // MIXTYPE0.FIELD4[3:0]
  // MIXTYPE0.FIELD5[3:0]
  // MIXTYPE0.FIELD6[3:0]
  // RWTYPE5[31:0]

  logic [31:0] hold_wd, hold_q;
  initial begin
    hw2reg.rwtype2.de = 1'b0;
    hw2reg.rwtype2.d  = 32'hxxxxxxxx;
    hw2reg.rwtype3.field0.de = 1'b0;
    hw2reg.rwtype3.field0.d  = 16'hxxxx;
    hw2reg.rwtype3.field1.de = 1'b0;
    hw2reg.rwtype3.field1.d  = 16'hxxxx;
    hw2reg.rotype0.de = 1'b0;
    hw2reg.rotype0.d  = 32'hxxxxxxxx;
    hw2reg.w1ctype2.de = 1'b0;
    hw2reg.w1ctype2.d  = 32'hxxxxxxxx;
    hw2reg.w1stype2.de = 1'b0;
    hw2reg.w1stype2.d  = 32'hxxxxxxxx;
    hw2reg.w0ctype2.de = 1'b0;
    hw2reg.w0ctype2.d  = 32'hxxxxxxxx;
    hw2reg.r0w1ctype2.de = 1'b0;
    hw2reg.r0w1ctype2.d  = 32'hxxxxxxxx;
    hw2reg.rctype0.de = 1'b0;
    hw2reg.rctype0.d  = 32'hxxxxxxxx;
    hw2reg.mixtype0.field1.de = 1'b0;
    hw2reg.mixtype0.field1.d  = 4'hx;
    hw2reg.mixtype0.field3.de = 1'b0;
    hw2reg.mixtype0.field3.d  = 4'hx;
    hw2reg.mixtype0.field4.de = 1'b0;
    hw2reg.mixtype0.field4.d  = 4'hx;
    hw2reg.mixtype0.field5.de = 1'b0;
    hw2reg.mixtype0.field5.d  = 4'hx;
    hw2reg.mixtype0.field6.de = 1'b0;
    hw2reg.mixtype0.field6.d  = 4'hx;
    hw2reg.rwtype5.de = 1'b0;
    hw2reg.rwtype5.d  = 32'hxxxxxxxx;
    my_rotype1_de = 1'b0;
    my_rotype1_d = 32'hxxxxxxxx;
    tl_h2d.a_valid = 1'b0;
    tl_h2d.a_opcode = Get;
    tl_h2d.a_user = 16'h0;
    repeat(20) @(posedge clk);
     ///////
    //
    // test RWTYPE0
    //
    // default value is 12345678
    test_rwtype0(12345678);
    // write value
    hold_wd = 32'hdeadbeef;
    send_wr(12'h0, hold_wd);
    test_rwtype0(hold_wd);
    // write opposite
    hold_wd = ~32'hdeadbeef;
    send_wr(12'h0, hold_wd);
    test_rwtype0(hold_wd);
     ///////
    //
    // test RWTYPE1
    //
    // default value is 32'h00006411
    test_rwtype1(32'h00006411);
    // write value
    hold_wd = 32'hdeadbeef;
    send_wr(12'h4, hold_wd);
    test_rwtype1(hold_wd);
    // write opposite
    hold_wd = ~32'hdeadbeef;
    send_wr(12'h4, hold_wd);
    test_rwtype1(hold_wd);
     ///////
    //
    // test RWTYPE2, RW + HRW
    //
    // default value is 0x04000400
    test_rwtype2(32'h04000400);
    // write value
    hold_wd = 32'hdeadbeef;
    send_wr(12'h8, hold_wd);
    test_rwtype2(hold_wd);
    // write opposite
    hold_wd = ~32'hdeadbeef;
    send_wr(12'h8, hold_wd);
    test_rwtype2(hold_wd);
    // write from HW side
    hold_wd = $urandom;
    hw2reg.rwtype2.de <= 1'b1;
    hw2reg.rwtype2.d  <= hold_wd;
    @(posedge clk);
    hw2reg.rwtype2.de <= 1'b0;
    hw2reg.rwtype2.d  <= 32'hxxxxxxxx;
    @(posedge clk);
    test_rwtype2(hold_wd);
    // write from HW side inverted
    hold_wd = ~hold_wd;
    hw2reg.rwtype2.de <= 1'b1;
    hw2reg.rwtype2.d  <= hold_wd;
    @(posedge clk);
    hw2reg.rwtype2.de <= 1'b0;
    hw2reg.rwtype2.d  <= 32'hxxxxxxxx;
    @(posedge clk);
    test_rwtype2(hold_wd);
    // try and get both the we and the de at the same time, we should win
    hold_wd = 32'haaaaaaaa;
    fork
      begin
        send_wr(12'h8, hold_wd);
      end
      begin
        hw2reg.rwtype2.de <= 1'b1;
        hw2reg.rwtype2.d  <= 32'h55555555;
        @(posedge clk);
        hw2reg.rwtype2.de <= 1'b0;
        hw2reg.rwtype2.d  <= 32'hxxxxxxxx;
      end
    join
    @(posedge clk);
    test_rwtype2(hold_wd);
     ///////
    //
    // test RWTYPE3, separate HRW fields
    //
    // default value is 0xee66cc55
    test_rwtype3(32'hee66cc55);
    // write value
    hold_wd = 32'hdeadbeef;
    send_wr(12'hc, hold_wd);
    test_rwtype3(hold_wd);
    // write opposite
    hold_wd = ~32'hdeadbeef;
    send_wr(12'hc, hold_wd);
    test_rwtype3(hold_wd);
    // write one field from HW side
    hold_q = hold_wd;
    hold_wd = $urandom;
    hw2reg.rwtype3.field0.de <= 1'b1;
    hw2reg.rwtype3.field0.d  <= hold_wd[15:0];
    @(posedge clk);
    hw2reg.rwtype3.field0.de <= 1'b0;
    hw2reg.rwtype3.field0.d  <= 16'hxxxx;
    @(posedge clk);
    test_rwtype3({hold_q[31:16],hold_wd[15:0]});
    // write other field from HW side
    hw2reg.rwtype3.field1.de <= 1'b1;
    hw2reg.rwtype3.field1.d  <= hold_wd[31:16];
    @(posedge clk);
    hw2reg.rwtype3.field1.de <= 1'b0;
    hw2reg.rwtype3.field1.d  <= 16'hxxxx;
    @(posedge clk);
    test_rwtype3(hold_wd);
    // write inverted
    hold_q = hold_wd;
    hold_wd = ~hold_wd;
    hw2reg.rwtype3.field1.de <= 1'b1;
    hw2reg.rwtype3.field1.d  <= hold_wd[31:16];
    @(posedge clk);
    hw2reg.rwtype3.field1.de <= 1'b0;
    hw2reg.rwtype3.field1.d  <= 16'hxxxx;
    @(posedge clk);
    test_rwtype3({hold_wd[31:16],hold_q[15:0]});
    // write other field from HW side
    hw2reg.rwtype3.field0.de <= 1'b1;
    hw2reg.rwtype3.field0.d  <= hold_wd[15:0];
    @(posedge clk);
    hw2reg.rwtype3.field0.de <= 1'b0;
    hw2reg.rwtype3.field0.d  <= 16'hxxxx;
    @(posedge clk);
    test_rwtype3(hold_wd);
    // try and get both the we and one de at the same time, we should win
    hold_q = 32'h55555555;
    hold_wd = 32'haaaaaaaa;
    fork
      begin
        send_wr(12'hc, hold_wd);
      end
      begin
        hw2reg.rwtype3.field0.de <= 1'b1;
        hw2reg.rwtype3.field0.d  <= hold_q[15:0];
        @(posedge clk);
        hw2reg.rwtype3.field0.de <= 1'b0;
        hw2reg.rwtype3.field0.d  <= 16'hxxxx;
      end
    join
    @(posedge clk);
    test_rwtype3(hold_wd);
    hold_q = 32'h77777777;
    hold_wd = 32'hcccccccc;
    fork
      begin
        send_wr(12'hc, hold_wd);
      end
      begin
        hw2reg.rwtype3.field1.de <= 1'b1;
        hw2reg.rwtype3.field1.d  <= hold_q[15:0];
        @(posedge clk);
        hw2reg.rwtype3.field1.de <= 1'b0;
        hw2reg.rwtype3.field1.d  <= 16'hxxxx;
      end
    join
    @(posedge clk);
    test_rwtype3(hold_wd);
     ///////
    //
    // test RWTYPE4
    //
    // default value is 80004000
    test_rwtype4(32'h80004000);
    // write value
    hold_wd = 32'hdeadbeef;
    send_wr(12'h200, hold_wd);
    test_rwtype4(hold_wd);
    // write opposite
    hold_wd = ~32'hdeadbeef;
    send_wr(12'h200, hold_wd);
    test_rwtype4(hold_wd);
     ///////
    //
    // test ROTYPE0
    //
    // default value is 0x11111111
    hold_wd = 32'h11111111;
    test_rotype0(hold_wd);
    // write value, should be ignored
    send_wr(12'h204, 32'hdeadbeef);
    test_rotype0(hold_wd);
    // write opposite
    send_wr(12'h204, ~32'hdeadbeef);
    test_rotype0(hold_wd);
    // write from HW side
    hold_wd = $urandom;
    hw2reg.rotype0.de <= 1'b1;
    hw2reg.rotype0.d  <= hold_wd;
    @(posedge clk);
    hw2reg.rotype0.de <= 1'b0;
    hw2reg.rotype0.d  <= 32'hxxxxxxxx;
    @(posedge clk);
    test_rotype0(hold_wd);
    // write from HW side inverted
    hold_wd = ~hold_wd;
    hw2reg.rotype0.de <= 1'b1;
    hw2reg.rotype0.d  <= hold_wd;
    @(posedge clk);
    hw2reg.rotype0.de <= 1'b0;
    hw2reg.rotype0.d  <= 32'hxxxxxxxx;
    @(posedge clk);
    test_rotype0(hold_wd);
     ///////
    //
    // test W1CTYPE0
    //
    // default value is 0xbbccddee
    hold_q = 32'hbbccddee;
    test_w1ctype0(hold_q);
    // write value, should clear those bits
    hold_wd = 32'hdeadbeef;
    hold_q &= ~hold_wd;
    send_wr(12'h208, hold_wd);
    test_w1ctype0(hold_q);
    // write opposite, should clear everything by now
    hold_wd = 32'hdeadbeef;
    hold_q &= ~hold_wd;
    send_wr(12'h208, hold_wd);
    test_w1ctype0(hold_q);
     ///////
    //
    // test W1CTYPE1
    //
    // default value is 0x7777eeee
    hold_q = 32'h7777eeee;
    test_w1ctype1(hold_q);
    // write value, should clear those bits
    hold_wd = 32'hdeadbeef;
    hold_q &= ~hold_wd;
    send_wr(12'h20c, hold_wd);
    test_w1ctype1(hold_q);
    // write opposite, shoudl clear everything by now
    hold_wd = ~32'hdeadbeef;
    hold_q &= ~hold_wd;
    send_wr(12'h20c, hold_wd);
    test_w1ctype1(hold_q);
     ///////
    //
    // test W1CTYPE2, W1C + HRW
    //
    // default value is 0xaa775566
    hold_q = 32'haa775566;
    test_w1ctype2(hold_q);
    // write value
    hold_wd = 32'hdeadbeef;
    hold_q &= ~hold_wd;
    send_wr(12'h210, hold_wd);
    test_w1ctype2(hold_q);
    // write opposite
    hold_wd = ~32'hdeadbeef;
    hold_q &= ~hold_wd;
    send_wr(12'h210, hold_wd);
    test_w1ctype2(hold_q);
    // write from HW side
    hold_wd = $urandom;
    hw2reg.w1ctype2.de <= 1'b1;
    hw2reg.w1ctype2.d  <= hold_wd;
    @(posedge clk);
    hw2reg.w1ctype2.de <= 1'b0;
    hw2reg.w1ctype2.d  <= 32'hxxxxxxxx;
    @(posedge clk);
    test_w1ctype2(hold_wd);
    // write from HW side inverted
    hold_wd = ~hold_wd;
    hw2reg.w1ctype2.de <= 1'b1;
    hw2reg.w1ctype2.d  <= hold_wd;
    @(posedge clk);
    hw2reg.w1ctype2.de <= 1'b0;
    hw2reg.w1ctype2.d  <= 32'hxxxxxxxx;
    @(posedge clk);
    test_w1ctype2(hold_wd);
    // write value
    hold_q = hold_wd;
    hold_wd = 32'hdeadbeef;
    hold_q &= ~hold_wd;
    send_wr(12'h210, hold_wd);
    test_w1ctype2(hold_q);
    // try and get both the we and the de at the same time, we should clear bits in d
    hold_wd = 32'h44444444;
    hold_q = 32'heeddbb77;
    fork
      begin
        send_wr(12'h210, hold_wd);
      end
      begin
        hw2reg.w1ctype2.de <= 1'b1;
        hw2reg.w1ctype2.d  <= hold_q;
        @(posedge clk);
        hw2reg.w1ctype2.de <= 1'b0;
        hw2reg.w1ctype2.d  <= 32'hxxxxxxxx;
      end
    join
    @(posedge clk);
    hold_q &= ~hold_wd;
    test_w1ctype2(hold_q);
     ///////
    //
    // test W1STYPE2, W1S + HRW
    //
    // default value is 0x11224488
    hold_q = 32'h11224488;
    test_w1stype2(hold_q);
    // write value
    hold_wd = 32'hdeadbeef;
    hold_q |= hold_wd;
    send_wr(12'h214, hold_wd);
    test_w1stype2(hold_q);
    // write opposite
    hold_wd = ~32'hdeadbeef;
    hold_q |= hold_wd;
    send_wr(12'h214, hold_wd);
    test_w1stype2(hold_q);
    // write from HW side
    hold_wd = $urandom;
    hw2reg.w1stype2.de <= 1'b1;
    hw2reg.w1stype2.d  <= hold_wd;
    @(posedge clk);
    hw2reg.w1stype2.de <= 1'b0;
    hw2reg.w1stype2.d  <= 32'hxxxxxxxx;
    @(posedge clk);
    test_w1stype2(hold_wd);
    // write from HW side inverted
    hold_wd = ~hold_wd;
    hw2reg.w1stype2.de <= 1'b1;
    hw2reg.w1stype2.d  <= hold_wd;
    @(posedge clk);
    hw2reg.w1stype2.de <= 1'b0;
    hw2reg.w1stype2.d  <= 32'hxxxxxxxx;
    @(posedge clk);
    test_w1stype2(hold_wd);
    // write value
    hold_q = hold_wd;
    hold_wd = 32'hdeadbeef;
    hold_q |= hold_wd;
    send_wr(12'h214, hold_wd);
    test_w1stype2(hold_q);
    // try and get both the we and the de at the same time, we should set bits in d
    hold_wd = 32'h44444444;
    hold_q = 32'h9955cc33;
    fork
      begin
        send_wr(12'h214, hold_wd);
      end
      begin
        hw2reg.w1stype2.de <= 1'b1;
        hw2reg.w1stype2.d  <= hold_q;
        @(posedge clk);
        hw2reg.w1stype2.de <= 1'b0;
        hw2reg.w1stype2.d  <= 32'hxxxxxxxx;
      end
    join
    @(posedge clk);
    hold_q |= hold_wd;
    test_w1stype2(hold_q);
     ///////
    //
    // test W0CTYPE2, W0C + HRW
    //
    // default value is 0xfec8137f
    hold_q = 32'hfec8137f;
    test_w0ctype2(hold_q);
    // write value
    hold_wd = 32'hdeadbeef;
    hold_q &= hold_wd;
    send_wr(12'h218, hold_wd);
    test_w0ctype2(hold_q);
    // write opposite
    hold_wd = ~32'hdeadbeef;
    hold_q &= hold_wd;
    send_wr(12'h218, hold_wd);
    test_w0ctype2(hold_q);
    // write from HW side
    hold_wd = $urandom;
    hw2reg.w0ctype2.de <= 1'b1;
    hw2reg.w0ctype2.d  <= hold_wd;
    @(posedge clk);
    hw2reg.w0ctype2.de <= 1'b0;
    hw2reg.w0ctype2.d  <= 32'hxxxxxxxx;
    @(posedge clk);
    test_w0ctype2(hold_wd);
    // write from HW side inverted
    hold_wd = ~hold_wd;
    hw2reg.w0ctype2.de <= 1'b1;
    hw2reg.w0ctype2.d  <= hold_wd;
    @(posedge clk);
    hw2reg.w0ctype2.de <= 1'b0;
    hw2reg.w0ctype2.d  <= 32'hxxxxxxxx;
    @(posedge clk);
    test_w0ctype2(hold_wd);
    // write value
    hold_q = hold_wd;
    hold_wd = 32'hdeadbeef;
    hold_q &= hold_wd;
    send_wr(12'h218, hold_wd);
    test_w0ctype2(hold_q);
    // try and get both the we and the de at the same time, we should set bits in d
    hold_wd = 32'hee77bbcc;
    hold_q = 32'hbcada8e4;
    fork
      begin
        send_wr(12'h218, hold_wd);
      end
      begin
        hw2reg.w0ctype2.de <= 1'b1;
        hw2reg.w0ctype2.d  <= hold_q;
        @(posedge clk);
        hw2reg.w0ctype2.de <= 1'b0;
        hw2reg.w0ctype2.d  <= 32'hxxxxxxxx;
      end
    join
    @(posedge clk);
    hold_q &= hold_wd;
    test_w0ctype2(hold_q);
     ///////
    //
    // test R0W1CTYPE2, R0W1C + HRW
    //
    // default value is 0xaa775566
    hold_q = 32'haa775566;
    test_r0w1ctype2(hold_q);
    // write value
    hold_wd = 32'hdeadbeef;
    hold_q &= ~hold_wd;
    send_wr(12'h21c, hold_wd);
    test_r0w1ctype2(hold_q);
    // write opposite
    hold_wd = ~32'hdeadbeef;
    hold_q &= ~hold_wd;
    send_wr(12'h21c, hold_wd);
    test_r0w1ctype2(hold_q);
    // write from HW side
    hold_wd = $urandom;
    hw2reg.r0w1ctype2.de <= 1'b1;
    hw2reg.r0w1ctype2.d  <= hold_wd;
    @(posedge clk);
    hw2reg.r0w1ctype2.de <= 1'b0;
    hw2reg.r0w1ctype2.d  <= 32'hxxxxxxxx;
    @(posedge clk);
    test_r0w1ctype2(hold_wd);
    // write from HW side inverted
    hold_wd = ~hold_wd;
    hw2reg.r0w1ctype2.de <= 1'b1;
    hw2reg.r0w1ctype2.d  <= hold_wd;
    @(posedge clk);
    hw2reg.r0w1ctype2.de <= 1'b0;
    hw2reg.r0w1ctype2.d  <= 32'hxxxxxxxx;
    @(posedge clk);
    test_r0w1ctype2(hold_wd);
    // write value
    hold_q = hold_wd;
    hold_wd = 32'hdeadbeef;
    hold_q &= ~hold_wd;
    send_wr(12'h21c, hold_wd);
    test_r0w1ctype2(hold_q);
    // try and get both the we and the de at the same time, we should clear bits in d
    hold_wd = 32'h44444444;
    hold_q = 32'heeddbb77;
    fork
      begin
        send_wr(12'h21c, hold_wd);
      end
      begin
        hw2reg.r0w1ctype2.de <= 1'b1;
        hw2reg.r0w1ctype2.d  <= hold_q;
        @(posedge clk);
        hw2reg.r0w1ctype2.de <= 1'b0;
        hw2reg.r0w1ctype2.d  <= 32'hxxxxxxxx;
      end
    join
    @(posedge clk);
    hold_q &= ~hold_wd;
    test_r0w1ctype2(hold_q);
     ///////
    //
    // test RCTYPE0 (read-only clear)
    //
    // default value is 0x77443399
    hold_wd = 32'h77443399;
    test_rctype0(hold_wd);
    // write value, should be ignored
    hold_wd = 32'hdeadbeef;
    send_wr(12'h220, hold_wd);
    test_rctype0(0);
    // write opposite
    hold_wd = ~32'hdeadbeef;
    send_wr(12'h220, hold_wd);
    test_rctype0(0);
    // write from HW side
    hold_wd = $urandom;
    hw2reg.rctype0.de <= 1'b1;
    hw2reg.rctype0.d  <= hold_wd;
    @(posedge clk);
    hw2reg.rctype0.de <= 1'b0;
    hw2reg.rctype0.d  <= 32'hxxxxxxxx;
    @(posedge clk);
    test_rctype0(hold_wd);
    // write from HW side inverted
    hold_wd = ~hold_wd;
    hw2reg.rctype0.de <= 1'b1;
    hw2reg.rctype0.d  <= hold_wd;
    @(posedge clk);
    hw2reg.rctype0.de <= 1'b0;
    hw2reg.rctype0.d  <= 32'hxxxxxxxx;
    @(posedge clk);
    test_rctype0(hold_wd);
     ///////
    //
    // test WOTYPE0
    //
    // default value is 0x11223344
    hold_wd = 32'h11223344;
    test_wotype0(hold_wd);
    // write value
    hold_wd = 32'hdeadbeef;
    send_wr(12'h224, hold_wd);
    test_wotype0(hold_wd);
    // write opposite
    hold_wd = ~32'hdeadbeef;
    send_wr(12'h224, hold_wd);
    test_wotype0(hold_wd);
     ///////
    //
    // test MIXTYPE0
    //
    // default value is 0x87654321
    hold_q = 32'h87654321;
    test_mixtype0(hold_q);
    // read cleared bits [27:24]
    hold_q  &= 32'hf0ffffff;
    // write value
    hold_wd = 32'h55555555;
    send_wr(12'h228, hold_wd);
    @(posedge clk);
    hold_q = { hold_wd[31:28],                  // write-only
                                hold_q[27:24],  // read-only-clear
               hold_wd[23:20] | hold_q[23:20],  // rw1s
              ~hold_wd[19:16] & hold_q[19:16],  // rw1c
                                hold_q[15:12],  // ro
                                hold_q[11: 8],  // ro
               hold_wd[ 7: 4],                  // rw
               hold_wd[ 3: 0]};                 // rw
    test_mixtype0(hold_q);
    // write opposite
    hold_wd = 32'haaaaaaaa;
    send_wr(12'h228, hold_wd);
    @(posedge clk);
    hold_q = { hold_wd[31:28],                  // write-only
                                hold_q[27:24],  // read-only-clear
               hold_wd[23:20] | hold_q[23:20],  // rw1s
              ~hold_wd[19:16] & hold_q[19:16],  // rw1c
                                hold_q[15:12],  // ro
                                hold_q[11: 8],  // ro
               hold_wd[ 7: 4],                  // rw
               hold_wd[ 3: 0]};                 // rw
    test_mixtype0(hold_q);
    repeat(2) begin
      // write one field at a time from HW side
      hold_wd = $urandom;
      // field 1
      $display("INFO: trying field[1] with %h", hold_wd);
      hw2reg.mixtype0.field1.de <= 1'b1;
      hw2reg.mixtype0.field1.d  <= hold_wd[7:4];
      @(posedge clk);
      hw2reg.mixtype0.field1.de <= 1'b0;
      hw2reg.mixtype0.field1.d  <= 4'hx;
      @(posedge clk);
      hold_q = {hold_q[31:8],hold_wd[7:4],hold_q[3:0]};
      test_mixtype0(hold_q);
      // field 3
      $display("INFO: trying field[3] with %h", hold_wd);
      hw2reg.mixtype0.field3.de <= 1'b1;
      hw2reg.mixtype0.field3.d  <= hold_wd[15:12];
      @(posedge clk);
      hw2reg.mixtype0.field3.de <= 1'b0;
      hw2reg.mixtype0.field3.d  <= 4'hx;
      @(posedge clk);
      hold_q = {hold_q[31:16],hold_wd[15:12],hold_q[11:0]};
      test_mixtype0(hold_q);
      // field 4
      $display("INFO: trying field[4] with %h", hold_wd);
      hw2reg.mixtype0.field4.de <= 1'b1;
      hw2reg.mixtype0.field4.d  <= hold_wd[19:16];
      @(posedge clk);
      hw2reg.mixtype0.field4.de <= 1'b0;
      hw2reg.mixtype0.field4.d  <= 4'hx;
      @(posedge clk);
      hold_q = {hold_q[31:20],hold_wd[19:16],hold_q[15:0]};
      test_mixtype0(hold_q);
      // field 5
      $display("INFO: trying field[5] with %h", hold_wd);
      hw2reg.mixtype0.field5.de <= 1'b1;
      hw2reg.mixtype0.field5.d  <= hold_wd[23:20];
      @(posedge clk);
      hw2reg.mixtype0.field5.de <= 1'b0;
      hw2reg.mixtype0.field5.d  <= 4'hx;
      @(posedge clk);
      hold_q = {hold_q[31:24],hold_wd[23:20],hold_q[19:0]};
      test_mixtype0(hold_q);
      // field 6
      $display("INFO: trying field[6] with %h", hold_wd);
      hw2reg.mixtype0.field6.de <= 1'b1;
      hw2reg.mixtype0.field6.d  <= hold_wd[27:24];
      @(posedge clk);
      hw2reg.mixtype0.field6.de <= 1'b0;
      hw2reg.mixtype0.field6.d  <= 4'hx;
      @(posedge clk);
      hold_q = {hold_q[31:28],hold_wd[27:24],hold_q[23:0]};
      test_mixtype0(hold_q);
      hold_q &= 32'hf0ffffff; // read-clear
    end
    // try and get both the we and the de's at the same time, we should win
    repeat(2) begin
      // bits [11:8] (field2) can never be changed
      hold_q  = ($urandom & 32'hfffff0ff) | (hold_q & 32'h00000f00);
      hold_wd = $urandom;
      $display("INFO: trying field collision with we %h de %h", hold_wd, hold_q);
      fork
        begin
          send_wr(12'h228, hold_wd);
        end
        begin
          hw2reg.mixtype0.field1.de <= 1'b1;
          hw2reg.mixtype0.field1.d  <= hold_q[7:4];
          hw2reg.mixtype0.field3.de <= 1'b1;
          hw2reg.mixtype0.field3.d  <= hold_q[15:12];
          hw2reg.mixtype0.field4.de <= 1'b1;
          hw2reg.mixtype0.field4.d  <= hold_q[19:16];
          hw2reg.mixtype0.field5.de <= 1'b1;
          hw2reg.mixtype0.field5.d  <= hold_q[23:20];
          hw2reg.mixtype0.field6.de <= 1'b1;
          hw2reg.mixtype0.field6.d  <= hold_q[27:24];
          @(posedge clk);
          hw2reg.mixtype0.field1.de <= 1'b0;
          hw2reg.mixtype0.field1.d  <= 4'hx;
          hw2reg.mixtype0.field3.de <= 1'b0;
          hw2reg.mixtype0.field3.d  <= 4'hx;
          hw2reg.mixtype0.field4.de <= 1'b0;
          hw2reg.mixtype0.field4.d  <= 4'hx;
          hw2reg.mixtype0.field5.de <= 1'b0;
          hw2reg.mixtype0.field5.d  <= 4'hx;
          hw2reg.mixtype0.field6.de <= 1'b0;
          hw2reg.mixtype0.field6.d  <= 4'hx;
        end
      join
      @(posedge clk);
      hold_q = { hold_wd[31:28],                  // write-only
                                  hold_q[27:24],  // read-only-clear
                 hold_wd[23:20] | hold_q[23:20],  // rw1s
                ~hold_wd[19:16] & hold_q[19:16],  // rw1c
                                  hold_q[15:12],  // ro
                                  hold_q[11: 8],  // ro
                 hold_wd[ 7: 4],                  // rw
                 hold_wd[ 3: 0]};                 // rw
      test_mixtype0(hold_q);
    end
     ///////
    //
    // test RWTYPE5, RW + HRW + HWQE
    // test that only sw writes effect captured value
    //
    // default value is 0xbabababa
    test_rwtype5(32'hbabababa);
    // write value
    hold_wd = 32'hdeadbeef;
    send_wr(12'h22c, hold_wd);
    test_rwtype5(hold_wd);
    test_rwtype5_capture(hold_wd);
    // write opposite
    hold_wd = ~32'hdeadbeef;
    send_wr(12'h22c, hold_wd);
    test_rwtype5(hold_wd);
    test_rwtype5_capture(hold_wd);
    // write from HW side
    hold_q = hold_wd;
    hold_wd = $urandom;
    hw2reg.rwtype5.de <= 1'b1;
    hw2reg.rwtype5.d  <= hold_wd;
    @(posedge clk);
    hw2reg.rwtype5.de <= 1'b0;
    hw2reg.rwtype5.d  <= 32'hxxxxxxxx;
    @(posedge clk);
    test_rwtype5(hold_wd);
    test_rwtype5_capture(hold_q);
    // write from HW side inverted
    hold_wd = ~hold_wd;
    hw2reg.rwtype5.de <= 1'b1;
    hw2reg.rwtype5.d  <= hold_wd;
    @(posedge clk);
    hw2reg.rwtype5.de <= 1'b0;
    hw2reg.rwtype5.d  <= 32'hxxxxxxxx;
    @(posedge clk);
    test_rwtype5(hold_wd);
    test_rwtype5_capture(hold_q);
    // try and get both the we and the de at the same time, we should win
    hold_wd = 32'haaaaaaaa;
    fork
      begin
        send_wr(12'h22c, hold_wd);
      end
      begin
        hw2reg.rwtype5.de <= 1'b1;
        hw2reg.rwtype5.d  <= 32'h55555555;
        @(posedge clk);
        hw2reg.rwtype5.de <= 1'b0;
        hw2reg.rwtype5.d  <= 32'hxxxxxxxx;
      end
    join
    @(posedge clk);
    test_rwtype5(hold_wd);
    test_rwtype5_capture(hold_wd);
     ///////
    //
    // test RWTYPE6, RW + HRW + HWEXT
    // create a true external register
    //
    // default value is 0xc8c8c8c8
    test_rwtype6(32'hc8c8c8c8);
    // write value
    hold_wd = 32'hdeadbeef;
    send_wr(12'h230, hold_wd);
    test_rwtype6(hold_wd);
    test_rwtype6_capture(hold_wd);
    // write opposite
    hold_wd = ~32'hdeadbeef;
    send_wr(12'h230, hold_wd);
    test_rwtype6(hold_wd);
    test_rwtype6_capture(hold_wd);
     ///////
    //
    // test ROTYPE1, RO + HRW + HWEXT
    // create a true external register, writable only by us
    //
    // default value is 0x66aa66aa
    hold_q = 32'h66aa66aa;
    test_rotype1(hold_q);
    // write value
    hold_wd = 32'hdeadbeef;
    send_wr(12'h234, hold_wd);
    test_rotype1(hold_q);
    test_rotype1_capture(hold_q);
    // write opposite
    hold_wd = ~32'hdeadbeef;
    send_wr(12'h234, hold_wd);
    test_rotype1(hold_q);
    test_rotype1_capture(hold_q);
    // simulate write from our side
    @(posedge clk);
    hold_wd = 32'h66778899;
    my_rotype1_de = 1'b1;
    my_rotype1_d = hold_wd;
    @(posedge clk);
    my_rotype1_de = 1'b0;
    my_rotype1_d = 32'hxxxxxxxx;
    @(posedge clk);
    test_rotype1(hold_wd);
    test_rotype1_capture(hold_wd);
    @(posedge clk);
    hold_wd = ~32'h66778899;
    my_rotype1_de = 1'b1;
    my_rotype1_d = hold_wd;
    @(posedge clk);
    my_rotype1_de = 1'b0;
    my_rotype1_d = 32'hxxxxxxxx;
    @(posedge clk);
    test_rotype1(hold_wd);
    test_rotype1_capture(hold_wd);
     ///////
    //
    // test ROTYPE2, RO + HWNONE
    //
    // constant value is 0x9b908a79
    hold_q = 32'h9b908a79;
    test_rotype2(hold_q);
    // write value
    hold_wd = 32'hdeadbeef;
    send_wr(12'h238, hold_wd);
    test_rotype2(hold_q);
    // write opposite
    hold_wd = ~32'hdeadbeef;
    send_wr(12'h238, hold_wd);
    test_rotype2(hold_q);
     ///////
    //
    // test RWTYPE7, RW + HWNONE
    //
    // default value is 0xf6f6f6f6
    test_rwtype7(32'hf6f6f6f6);
    // write value
    hold_wd = 32'hdeadbeef;
    send_wr(12'h23c, hold_wd);
    test_rwtype7(hold_wd);
    // write opposite
    hold_wd = ~32'hdeadbeef;
    send_wr(12'h23c, hold_wd);
    test_rwtype7(hold_wd);

    $display("INFO: test completed with %d errors", errorcount);
    dv_test_status_pkg::dv_test_status(.passed(errorcount == 0));
  end

endmodule
