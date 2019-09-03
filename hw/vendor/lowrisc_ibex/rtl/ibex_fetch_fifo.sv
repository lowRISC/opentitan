// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Fetch Fifo for 32 bit memory interface
 *
 * input port: send address one cycle before the data
 * clear_i clears the FIFO for the following cycle. in_addr_i can be sent in
 * this cycle already.
 */
module ibex_fetch_fifo (
    input  logic        clk_i,
    input  logic        rst_ni,

    // control signals
    input  logic        clear_i,          // clears the contents of the fifo

    // input port
    input  logic [31:0] in_addr_i,
    input  logic [31:0] in_rdata_i,
    input  logic        in_err_i,
    input  logic        in_valid_i,
    output logic        in_ready_o,


    // output port
    output logic        out_valid_o,
    input  logic        out_ready_i,
    output logic [31:0] out_rdata_o,
    output logic [31:0] out_addr_o,
    output logic        out_err_o,

    output logic        out_valid_stored_o // same as out_valid_o, except that if something is
                                           // incoming now it is not included. This signal is
                                           // available immediately as it comes directly out of FFs
);

  localparam int unsigned DEPTH = 3; // must be 3 or greater

  // index 0 is used for output
  logic [DEPTH-1:0] [31:0]  addr_n,    addr_int,    addr_q;
  logic [DEPTH-1:0] [31:0]  rdata_n,   rdata_int,   rdata_q;
  logic [DEPTH-1:0]         err_n,     err_int,     err_q;
  logic [DEPTH-1:0]         valid_n,   valid_int,   valid_q;

  logic             [31:2]  addr_next;
  logic             [31:0]  rdata, rdata_unaligned;
  logic                     err,   err_unaligned;
  logic                     valid, valid_unaligned;

  logic                     aligned_is_compressed, unaligned_is_compressed;
  logic                     unaligned_is_compressed_st;

  /////////////////
  // Output port //
  /////////////////


  assign rdata = valid_q[0] ? rdata_q[0] : in_rdata_i;
  assign err   = valid_q[0] ? err_q[0]   : in_err_i;
  assign valid = valid_q[0] | in_valid_i;

  assign rdata_unaligned = valid_q[1] ? {rdata_q[1][15:0], rdata[31:16]} :
                                        {in_rdata_i[15:0], rdata[31:16]};
  // If entry[1] is valid, an error can come from entry[0] or entry[1], unless the
  // instruction in entry[0] is compressed (entry[1] is a new instruction)
  // If entry[1] is not valid, and entry[0] is, an error can come from entry[0] or the incoming
  // data, unless the instruction in entry[0] is compressed
  // If entry[0] is not valid, the error must come from the incoming data
  assign err_unaligned   = valid_q[1] ? ((err_q[1] & ~unaligned_is_compressed) | err_q[0]) :
                                        ((valid_q[0] & err_q[0]) |
                                         (in_err_i & (~valid_q[0] | ~unaligned_is_compressed)));
  // An uncompressed unaligned instruction is only valid if both parts are available
  assign valid_unaligned = valid_q[1] ? 1'b1 :
                                        (valid_q[0] & in_valid_i);

  assign unaligned_is_compressed    = rdata[17:16] != 2'b11;
  assign aligned_is_compressed      = rdata[ 1: 0] != 2'b11;
  assign unaligned_is_compressed_st = rdata_q[0][17:16] != 2'b11;

  ////////////////////////////////////////
  // Instruction aligner (if unaligned) //
  ////////////////////////////////////////

  always_comb begin
    // serve the aligned case even though the output address is unaligned when
    // the next instruction will be from a hardware loop target
    // in this case the current instruction is already prealigned in element 0
    if (out_addr_o[1]) begin
      // unaligned case
      out_rdata_o = rdata_unaligned;
      out_err_o   = err_unaligned;

      if (unaligned_is_compressed) begin
        out_valid_o = valid;
      end else begin
        out_valid_o = valid_unaligned;
      end
    end else begin
      // aligned case
      out_rdata_o = rdata;
      out_err_o   = err;
      out_valid_o = valid;
    end
  end

  assign out_addr_o = valid_q[0] ? addr_q[0] : in_addr_i;

  // this valid signal must not depend on signals from outside!
  always_comb begin
    out_valid_stored_o = 1'b1;

    if (out_addr_o[1]) begin
      if (unaligned_is_compressed_st) begin
        out_valid_stored_o = 1'b1;
      end else begin
        out_valid_stored_o = valid_q[1];
      end
    end else begin
      out_valid_stored_o = valid_q[0];
    end
  end


  ////////////////
  // input port //
  ////////////////

  // we accept data as long as our fifo is not full
  // we don't care about clear here as the data will be received one cycle
  // later anyway
  assign in_ready_o = ~valid_q[DEPTH-2];

  /////////////////////
  // FIFO management //
  /////////////////////

  always_comb begin
    addr_int    = addr_q;
    rdata_int   = rdata_q;
    err_int     = err_q;
    valid_int   = valid_q;
    if (in_valid_i) begin
      for (int j = 0; j < DEPTH; j++) begin
        if (!valid_q[j]) begin
          addr_int[j]  = in_addr_i;
          rdata_int[j] = in_rdata_i;
          err_int[j]   = in_err_i;
          valid_int[j] = 1'b1;
          break;
        end
      end
    end
  end

  assign addr_next[31:2] = addr_int[0][31:2] + 30'h1;

  // move everything by one step
  always_comb begin
    addr_n     = addr_int;
    rdata_n    = rdata_int;
    err_n      = err_int;
    valid_n    = valid_int;

    if (out_ready_i && out_valid_o) begin
      if (addr_int[0][1]) begin
        // unaligned case
        if (unaligned_is_compressed) begin
          addr_n[0] = {addr_next[31:2], 2'b00};
        end else begin
          addr_n[0] = {addr_next[31:2], 2'b10};
        end

        rdata_n  = {32'b0, rdata_int[DEPTH-1:1]};
        err_n    = {1'b0,  err_int[DEPTH-1:1]};
        valid_n  = {1'b0,  valid_int[DEPTH-1:1]};
      end else if (aligned_is_compressed) begin
        // just increase address, do not move to next entry in FIFO
        addr_n[0] = {addr_int[0][31:2], 2'b10};
      end else begin
        // move to next entry in FIFO
        addr_n[0] = {addr_next[31:2], 2'b00};
        rdata_n   = {32'b0, rdata_int[DEPTH-1:1]};
        err_n     = {1'b0,  err_int[DEPTH-1:1]};
        valid_n   = {1'b0,  valid_int[DEPTH-1:1]};
      end
    end
  end

  ///////////////
  // registers //
  ///////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_q    <= '{default: '0};
      rdata_q   <= '{default: '0};
      err_q     <= '0;
      valid_q   <= '0;
    end else begin
      // on a clear signal from outside we invalidate the content of the FIFO
      // completely and start from an empty state
      if (clear_i) begin
        valid_q   <= '0;
      end else begin
        addr_q    <= addr_n;
        rdata_q   <= rdata_n;
        err_q     <= err_n;
        valid_q   <= valid_n;
      end
    end
  end

  ////////////////
  // Assertions //
  ////////////////
`ifndef VERILATOR
  assert property (
    @(posedge clk_i) (in_valid_i) |-> ((valid_q[DEPTH-1] == 1'b0) || (clear_i == 1'b1)) );
`endif
endmodule
