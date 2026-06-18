// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  import rram_ctrl_pkg::*;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;

  logic clk, rst_n;
  logic init_done;
  wire rram_test_analog;

  tlul_pkg::tl_h2d_t prim_tl_h2d;
  tlul_pkg::tl_d2h_t prim_tl_d2h;

  rram_macro_req_t rram_macro_req;
  rram_macro_rsp_t rram_macro_rsp;

  logic [DataWidth-1:0] rdata, data;
  logic [AddrW-1:0] addr;
  logic info;
  int num_words;
  int errors = 0;

  assign (pull1, pull0) rram_test_analog = 1'b0;

  initial begin
    clk = '0;
    rst_n = '0;
    #100ns;
    rst_n = 1'b1;

    forever begin
      clk = ~clk;
      #10ns;
    end
  end

  task static wait_ack();
    #1ns;
    while (rram_macro_rsp.ack == 1'b0) begin
      @(posedge clk);
      #1ns;
    end
    if (rram_macro_rsp.done == 0) begin
      @(posedge clk);
      #1ns;
    end
  endtask

  task static wait_done();
    #1ns;
    while (rram_macro_rsp.done == 1'b0) begin
      @(posedge clk);
      #1ns;
    end
  endtask

  task automatic rram_store_buf(input logic [AddrW-1:0] addr, input logic [DataWidth-1:0] data);
    @(posedge clk);
    #1ns;
    rram_macro_req.wr_req = 1'b1;
    rram_macro_req.wr_last = 1'b0;
    rram_macro_req.addr = addr;
    rram_macro_req.wr_data = data;
    #1ns;
    wait_ack();
    if (rram_macro_rsp.done == 1'b0) begin
      rram_macro_req.wr_req = 1'b0;
      wait_done();
    end else begin
      @(posedge clk);
      #1ns;
      rram_macro_req.wr_req = 1'b0;
    end
  endtask

  task automatic rram_write(input logic [AddrW-1:0] addr, input logic info);
    @(posedge clk);
    #1ns;
    rram_macro_req.wr_req = 1'b1;
    rram_macro_req.wr_last = 1'b1;
    rram_macro_req.addr = addr;
    rram_macro_req.part = info ? RramPartInfo : RramPartData;
    wait_ack();
    rram_macro_req.wr_req = 1'b0;
    rram_macro_req.wr_last = 1'b0;
    wait_done();
  endtask

  task automatic rram_read(input logic [AddrW-1:0] addr, input logic info,
                           output logic [DataWidth-1:0] rdata);
    @(posedge clk);
    #1ns;
    rram_macro_req.rd_req = 1'b1;
    rram_macro_req.addr = addr;
    rram_macro_req.part = info ? RramPartInfo : RramPartData;
    wait_ack();
    rram_macro_req.rd_req = 1'b0;
    wait_done();
    rdata = rram_macro_rsp.rd_data;
    @(posedge clk);
  endtask

  task automatic rram_access_test(input logic [AddrW-1:0] addr, input logic info,
                                  input integer num_words);
    for (int unsigned k = 0; k < num_words; k++) begin
      rram_store_buf(addr + k, addr + k);
    end
    rram_write(addr, info);
    for (int unsigned k = 0; k < num_words; k++) begin
      data = addr + k;
      rram_read(addr + k, info, rdata);
      if (data !== rdata) begin
        $error("RRAM-ERROR: rdata[%0d]=%x, exp=%x", k, rdata, data);
        errors++;
      end
    end
  endtask

  initial begin
    prim_tl_h2d.a_valid = 1'b0;

    rram_macro_req.rd_req = '0;
    rram_macro_req.wr_req = '0;
    rram_macro_req.wr_last = '0;
    rram_macro_req.addr = '0;
    rram_macro_req.wr_data = '0;
    rram_macro_req.part = RramPartData;

    @(rst_n);
    @(init_done == 1'b1);
    #10ns;

    for (int i = 0; i < 100; i++) begin
      @(posedge clk);
      info = $urandom();
      addr = $urandom();
      addr[4:0] = '0;
      num_words = $urandom_range(1, MaxWrWords);
      rram_access_test(addr, info, num_words);
    end
    #10us;

    if (errors == 0) begin
      $display("TEST PASSED CHECKS");
    end
    $finish();
  end

  rram_macro #(
    .TotalPages(rram_ctrl_pkg::TotalPages),
    .DataWidth(rram_ctrl_pkg::DataWidth),
    .WordsPerPage(rram_ctrl_pkg::WordsPerPage),
    .TotalInfoPages(rram_ctrl_pkg::TotalInfoPages),
    .MaxWrWords(rram_ctrl_pkg::MaxWrWords)
  ) dut (
    .clk_i              (clk),
    .rst_ni             (rst_n),
    .rram_macro_i       (rram_macro_req),
    .rram_macro_o       (rram_macro_rsp),
    .cio_tck_i          ('0),
    .cio_tdi_i          ('0),
    .cio_tms_i          ('0),
    .cio_tdo_o          (),
    .cio_tdo_en_o       (),
    .lc_nvm_debug_en_i  (lc_ctrl_pkg::On),
    .scanmode_i         (MuBi4False),
    .scan_en_i          (1'b0),
    .scan_rst_ni        (1'b0),
    .rram_test_analog_io(rram_test_analog),
    .prim_tl_i          (prim_tl_h2d),
    .prim_tl_o          (prim_tl_d2h),
    .obs_ctrl_i         ('0),
    .rram_obs_o         ()
  );

  assign init_done = rram_macro_rsp.init_done;

endmodule
