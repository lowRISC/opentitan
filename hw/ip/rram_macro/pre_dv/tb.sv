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

  // Test/observability ports not exercised by the shared data-path tests below: JTAG, scan, BIST
  // lifecycle gating, and AST observability.
  // A vendor-specific test can drive any of them directly, from run_vendor_tests().
  logic cio_tck, cio_tdi, cio_tms, cio_tdo, cio_tdo_en;
  lc_ctrl_pkg::lc_tx_t lc_nvm_debug_en;
  prim_mubi_pkg::mubi4_t scanmode;
  logic scan_en, scan_rst_n;
  ast_pkg::ast_obs_ctrl_t obs_ctrl;
  logic [7:0] rram_obs;

  // rram_test_analog defaults to a weak pull-down, idle unless a vendor-specific test drives it
  // from run_vendor_tests().
  logic rram_test_analog_drv, rram_test_analog_drv_en;
  assign (pull1, pull0) rram_test_analog = 1'b0;
  assign rram_test_analog = rram_test_analog_drv_en ? rram_test_analog_drv : 1'bz;

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

  // Runs the data-path smoke test (random read/load/write) for `iter` iterations.
  task automatic test_func(input int iter);
    int errors_before;
    $display("Starting test test_func(%0d)", iter);
    errors_before = errors;
    for (int i = 0; i < iter; i++) begin
      @(posedge clk);
      info = $urandom();
      addr = $urandom();
      addr[4:0] = '0;
      num_words = $urandom_range(1, MaxWrWords);
      rram_access_test(addr, info, num_words);
    end
    $display("test_func(%0d): %s", iter, (errors == errors_before) ? "PASS" : "FAIL");
  endtask

  // Allows a specific vendor implementation to include its own additional tests, run via
  // run_vendor_tests() in the main initial block below.
  `include "rram_macro_vendor_tests.svh"

  initial begin
    cio_tck                 = 1'b0;
    cio_tdi                 = 1'b0;
    cio_tms                 = 1'b0;
    rram_test_analog_drv    = 1'b0;
    rram_test_analog_drv_en = 1'b0;
    lc_nvm_debug_en         = lc_ctrl_pkg::On;
    scanmode                = MuBi4False;
    scan_en                 = 1'b0;
    scan_rst_n              = 1'b0;
    obs_ctrl                = '0;

    prim_tl_h2d.a_valid   = 1'b0;
    prim_tl_h2d.a_opcode  = tlul_pkg::PutFullData;
    prim_tl_h2d.a_param   = '0;
    prim_tl_h2d.a_size    = 2'h2;
    prim_tl_h2d.a_source  = '0;
    prim_tl_h2d.a_address = '0;
    prim_tl_h2d.a_mask    = '0;
    prim_tl_h2d.a_data    = '0;
    prim_tl_h2d.a_user    = tlul_pkg::TL_A_USER_DEFAULT;
    prim_tl_h2d.d_ready   = 1'b1;

    rram_macro_req.rd_req = '0;
    rram_macro_req.wr_req = '0;
    rram_macro_req.wr_last = '0;
    rram_macro_req.addr = '0;
    rram_macro_req.wr_data = '0;
    rram_macro_req.part = RramPartData;
    rram_macro_req.ecc_en = '0;

    // wait for reset release
    @(rst_n);

    // wait for auto-initialization to complete
    @(init_done == 1'b1);
    #10ns;

    // run functional tests
    test_func(100);

    // run vendor specific tests
    run_vendor_tests();

    #10us;

    if (errors == 0) begin
      $display("TEST PASSED CHECKS");
    end
    $finish();
  end

  rram_macro #(
    .TotalDataPages(rram_ctrl_pkg::TotalDataPages),
    .DataWidth(rram_ctrl_pkg::DataWidth),
    .WordsPerPage(rram_ctrl_pkg::WordsPerPage),
    .TotalInfoPages(rram_ctrl_pkg::TotalInfoPages),
    .MaxWrWords(rram_ctrl_pkg::MaxWrWords)
  ) dut (
    .clk_i              (clk),
    .rst_ni             (rst_n),
    .rram_macro_i       (rram_macro_req),
    .rram_macro_o       (rram_macro_rsp),
    .cio_tck_i          (cio_tck),
    .cio_tdi_i          (cio_tdi),
    .cio_tms_i          (cio_tms),
    .cio_tdo_o          (cio_tdo),
    .cio_tdo_en_o       (cio_tdo_en),
    .lc_nvm_debug_en_i  (lc_nvm_debug_en),
    .scanmode_i         (scanmode),
    .scan_en_i          (scan_en),
    .scan_rst_ni        (scan_rst_n),
    .rram_test_analog_io(rram_test_analog),
    .prim_tl_i          (prim_tl_h2d),
    .prim_tl_o          (prim_tl_d2h),
    .obs_ctrl_i         (obs_ctrl),
    .rram_obs_o         (rram_obs)
  );

  assign init_done = rram_macro_rsp.init_done;

endmodule
