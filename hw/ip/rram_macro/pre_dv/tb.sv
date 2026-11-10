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
  logic [2:0] ecc_err;
  logic [AddrW-1:0] addr;
  logic info;
  logic ecc_en;
  int num_words;
  int errors = 0;

  // Test/observability ports not exercised by the shared data-path tests below: JTAG, scan, BIST
  // lifecycle gating, and AST observability.
  // The JTAG inputs (cio_tck/tdi/tms) are driven by the vendor tests include.
  // They are packed into the dut's jtag struct below, with trst_n held inactive.
  logic cio_tck, cio_tdi, cio_tms, cio_tdo, cio_tdo_en;
  jtag_pkg::jtag_req_t jtag_req;
  jtag_pkg::jtag_rsp_t jtag_rsp;
  assign jtag_req   = '{tck: cio_tck, tms: cio_tms, trst_n: 1'b1, tdi: cio_tdi};
  assign cio_tdo    = jtag_rsp.tdo;
  assign cio_tdo_en = jtag_rsp.tdo_oe;
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

  // Like rram_ctrl, every load request carries the partition of the write operation.
  task automatic rram_store_buf(input logic [AddrW-1:0] addr, input logic [DataWidth-1:0] data,
                                input logic ecc_en = 1'b0, input logic info = 1'b0);
    @(posedge clk);
    #1ns;
    rram_macro_req.wr_req = 1'b1;
    rram_macro_req.wr_last = 1'b0;
    rram_macro_req.addr = addr;
    rram_macro_req.part = info ? RramPartInfo : RramPartData;
    rram_macro_req.ecc_en = ecc_en;
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

  task automatic rram_write(input logic [AddrW-1:0] addr, input logic info,
                            input logic ecc_en = 1'b0);
    @(posedge clk);
    #1ns;
    rram_macro_req.wr_req = 1'b1;
    rram_macro_req.wr_last = 1'b1;
    rram_macro_req.addr = addr;
    rram_macro_req.ecc_en = ecc_en;
    rram_macro_req.part = info ? RramPartInfo : RramPartData;
    wait_ack();
    rram_macro_req.wr_req = 1'b0;
    rram_macro_req.wr_last = 1'b0;
    wait_done();
  endtask

  // Also returns the ECC error flags, sampled together with the read data.
  task automatic rram_read(input logic [AddrW-1:0] addr, input logic info,
                           output logic [DataWidth-1:0] rdata, output logic [2:0] ecc_err,
                           input logic ecc_en = 1'b0);
    @(posedge clk);
    #1ns;
    rram_macro_req.rd_req = 1'b1;
    rram_macro_req.addr = addr;
    rram_macro_req.ecc_en = ecc_en;
    rram_macro_req.part = info ? RramPartInfo : RramPartData;
    wait_ack();
    rram_macro_req.rd_req = 1'b0;
    wait_done();
    rdata = rram_macro_rsp.rd_data;
    ecc_err = rram_macro_rsp.ecc_err;
    @(posedge clk);
  endtask

  // Writes num_words words starting at addr and reads them back, all with the given ecc_en.
  // The words are written without errors, so no read may report an ECC error.
  task automatic rram_access_test(input logic [AddrW-1:0] addr, input logic info,
                                  input integer num_words, input logic ecc_en);
    for (int unsigned k = 0; k < num_words; k++) begin
      rram_store_buf(addr + k, addr + k, ecc_en, info);
    end
    rram_write(addr, info, ecc_en);
    for (int unsigned k = 0; k < num_words; k++) begin
      data = addr + k;
      rram_read(addr + k, info, rdata, ecc_err, ecc_en);
      if (data !== rdata) begin
        $error("RRAM-ERROR: rdata[%0d]=%x, exp=%x", k, rdata, data);
        errors++;
      end
      if (ecc_err !== 3'b000) begin
        $error("RRAM-ERROR: ecc_err[%0d]=%b with ecc_en=%b, exp=000", k, ecc_err, ecc_en);
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
      ecc_en = $urandom();
      addr = $urandom();
      addr[4:0] = '0;
      // Info accesses stay within the info array, and skip the marker page, so that random data
      // does not change the markers.
      if (info) begin
        addr = addr % (TotalInfoPages * WordsPerPage);
        if (addr[WordW +: InfoPageW] == MarkerInfoPage) begin
          addr[WordW +: InfoPageW] = MarkerInfoPage + 1'b1;
        end
      end
      num_words = $urandom_range(1, MaxWrWords);
      rram_access_test(addr, info, num_words, ecc_en);
    end
    $display("test_func(%0d): %s", iter, (errors == errors_before) ? "PASS" : "FAIL");
  endtask

  ////////////////////////
  // Marker read at init //
  ////////////////////////

  prim_mubi_pkg::mubi8_t allow_vol_unlock, cp_done;

  function automatic logic [AddrW-1:0] marker_addr(input logic [WordW-1:0] word);
    return AddrW'({MarkerInfoPage, word});
  endfunction

  // Writes a single word of the marker page and returns the error flag of the write.
  task automatic write_marker_word(input logic [WordW-1:0] word, input logic [DataWidth-1:0] val,
                                   output logic err, input logic ecc_en = 1'b1);
    rram_store_buf(marker_addr(word), val, ecc_en, 1'b1);
    rram_write(marker_addr(word), 1'b1, ecc_en);
    err = rram_macro_rsp.err;
  endtask

  task automatic expect_marker_write(input logic [WordW-1:0] word, input logic [DataWidth-1:0] val,
                                     input logic exp_err, input logic ecc_en = 1'b1);
    logic err;
    write_marker_word(word, val, err, ecc_en);
    if (err !== exp_err) begin
      $error("RRAM-ERROR: marker word %0d write err=%b, exp=%b", word, err, exp_err);
      errors++;
    end
  endtask

  task automatic expect_marker_word(input logic [WordW-1:0] word, input logic [DataWidth-1:0] exp);
    rram_read(marker_addr(word), 1'b1, rdata, ecc_err, 1'b1);
    if (rdata !== exp || ecc_err !== 3'b000) begin
      $error("RRAM-ERROR: marker word %0d=%x ecc_err=%b, exp=%x", word, rdata, ecc_err, exp);
      errors++;
    end
  endtask

  // Resets the macro, so that it reads the markers again, and waits for init_done.
  task automatic reset_dut();
    @(posedge clk);
    rst_n = 1'b0;
    repeat (5) @(posedge clk);
    rst_n = 1'b1;
    wait (init_done == 1'b1);
    #10ns;
  endtask

  // An invalid expected value only checks that the value is invalid.
  task automatic expect_markers(input prim_mubi_pkg::mubi8_t exp_allow,
                                input prim_mubi_pkg::mubi8_t exp_cp_done);
    if (prim_mubi_pkg::mubi8_test_invalid(exp_allow) ?
        !prim_mubi_pkg::mubi8_test_invalid(allow_vol_unlock) :
        allow_vol_unlock !== exp_allow) begin
      $error("RRAM-ERROR: allow_vol_unlock=%x, exp=%x", allow_vol_unlock,
             exp_allow);
      errors++;
    end
    if (prim_mubi_pkg::mubi8_test_invalid(exp_cp_done) ?
        !prim_mubi_pkg::mubi8_test_invalid(cp_done) :
        cp_done !== exp_cp_done) begin
      $error("RRAM-ERROR: cp_done=%x, exp=%x", cp_done, exp_cp_done);
      errors++;
    end
  endtask

  // Checks whether the zero view is on with a write and read of a data word outside of the marker
  // page.
  // With the zero view, the write fails and the read returns 0 with clean ECC.
  // Without it, the write succeeds and the word reads back.
  task automatic check_zero_view(input logic exp_on);
    localparam logic [AddrW-1:0] Addr = AddrW'(100 * WordsPerPage);
    localparam logic [DataWidth-1:0] Val = {DataWidth/16{16'hA55A}};
    logic err;
    rram_store_buf(Addr, Val, 1'b1);
    rram_write(Addr, 1'b0, 1'b1);
    err = rram_macro_rsp.err;
    if (err !== exp_on) begin
      $error("RRAM-ERROR: zero view %0d: data write err=%b, exp=%b", exp_on, err, exp_on);
      errors++;
    end
    rram_read(Addr, 1'b0, rdata, ecc_err, 1'b1);
    if (rdata !== (exp_on ? '0 : Val) || ecc_err !== 3'b000) begin
      $error("RRAM-ERROR: zero view %0d: data read %x ecc_err=%b", exp_on, rdata, ecc_err);
      errors++;
    end
  endtask

  // Writes the markers through the data path, and checks the latched values after each reset.
  task automatic test_markers();
    // The marker words as rram_ctrl writes them: the magic value XORed with the bus word addresses.
    localparam logic [DataWidth-1:0] DisVal =
        marker_word_value(MarkerMagic, DisVolRawUnlockWords[0]);
    localparam logic [DataWidth-1:0] CpDoneVal = marker_word_value(MarkerMagic, CpDoneWords[0]);
    // The magic value with an extra bit set outside of the 16 magic bits.
    localparam logic [DataWidth-1:0] DisValExtraBit = DisVal | (DataWidth'(1) << (DataWidth - 1));
    logic err;
    int errors_before;
    $display("Starting test test_markers");
    errors_before = errors;

    // Start from an all-zero marker page, like after forming.
    for (int unsigned k = 0; k < NumMarkerCopies; k++) begin
      write_marker_word(DisVolRawUnlockWords[k], '0, err);
      write_marker_word(CpDoneWords[k], '0, err);
    end
    reset_dut();
    expect_markers(prim_mubi_pkg::MuBi8True, prim_mubi_pkg::MuBi8False);
    // DIS_VOL_RAW_UNLOCK is not set, so the zero view is on.
    check_zero_view(1'b1);

    // The magic value without the address infection does not count.
    expect_marker_write(DisVolRawUnlockWords[0], DataWidth'(MarkerMagic),
                        1'b0);
    reset_dut();
    expect_markers(prim_mubi_pkg::MuBi8True, prim_mubi_pkg::MuBi8False);

    // A marker only counts if the whole word holds exactly the magic value.
    // The CP_DONE word is not the magic value, so CP_DONE is not set either.
    expect_marker_write(DisVolRawUnlockWords[0], DisValExtraBit, 1'b0);
    expect_marker_write(CpDoneWords[0], 'h1, 1'b0);
    reset_dut();
    expect_markers(prim_mubi_pkg::MuBi8True, prim_mubi_pkg::MuBi8False);

    // The magic value sets DIS_VOL_RAW_UNLOCK.
    // CP_DONE stays not set, since its word is still not the magic value.
    expect_marker_write(DisVolRawUnlockWords[0], DisVal, 1'b0);
    reset_dut();
    expect_markers(prim_mubi_pkg::MuBi8False, prim_mubi_pkg::MuBi8False);
    // DIS_VOL_RAW_UNLOCK is set, so the zero view is off.
    check_zero_view(1'b0);

    // The magic value sets CP_DONE.
    expect_marker_write(CpDoneWords[0], CpDoneVal, 1'b0);
    reset_dut();
    expect_markers(prim_mubi_pkg::MuBi8False, prim_mubi_pkg::MuBi8True);
    // rram_macro does not protect the marker page itself, rram_ctrl does.
    // So a set marker can be written again.
    expect_marker_write(CpDoneWords[0], '0, 1'b0);
    expect_marker_word(CpDoneWords[0], '0);

    // Other words of the marker page are writable too.
    expect_marker_write(WordW'(NumMarkerCopies * 2), 'h1234, 1'b0);
    expect_marker_word(WordW'(NumMarkerCopies * 2), 'h1234);

    $display("test_markers: %s", (errors == errors_before) ? "PASS" : "FAIL");
  endtask

  // Allows a specific vendor implementation to include its own additional tests, run via
  // run_vendor_tests() in the main initial block below.
  `include "rram_macro_vendor_tests.svh"

  initial begin
    rram_test_analog_drv    = 1'b0;
    rram_test_analog_drv_en = 1'b0;
    lc_nvm_debug_en         = lc_ctrl_pkg::Off;
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

    // Run the marker test first.
    // It starts without any marker, under the zero view, and leaves both markers set.
    // So the other tests run without the zero view.
    test_markers();

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
    .allow_vol_unlock_o (allow_vol_unlock),
    .cp_done_o          (cp_done),
    .jtag_i             (jtag_req),
    .jtag_o             (jtag_rsp),
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
