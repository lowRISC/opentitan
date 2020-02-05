// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Dual-port SRAM Wrapper
//   This module to connect SRAM interface to actual SRAM interface
//   At this time, it doesn't utilize ECC or any pipeline.
//   This module stays to include any additional calculation logic later on.
//   Instantiating SRAM is up to the top design to remove process dependency.

// Parameter
//   EnableECC:
//   EnableParity:
//   EnableInputPipeline:
//   EnableOutputPipeline:

`include "prim_assert.sv"

module prim_ram_2p_adv #(
  parameter int Depth = 512,
  parameter int Width = 32,
  parameter int CfgW = 8,     // WTC, RTC, etc

  // Configurations
  parameter bit EnableECC            = 0,
  parameter bit EnableParity         = 0,
  parameter bit EnableInputPipeline  = 0,
  parameter bit EnableOutputPipeline = 0,

  parameter MemT = "REGISTER", // can be "REGISTER" or "SRAM"

  // Do not touch
  parameter int SramAw = $clog2(Depth)
) (
  input clk_i,
  input rst_ni,

  input                     a_req_i,
  input                     a_write_i,
  input        [SramAw-1:0] a_addr_i,
  input        [Width-1:0]  a_wdata_i,
  output logic              a_rvalid_o,
  output logic [Width-1:0]  a_rdata_o,
  output logic [1:0]        a_rerror_o,

  input                     b_req_i,
  input                     b_write_i,
  input        [SramAw-1:0] b_addr_i,
  input        [Width-1:0]  b_wdata_i,
  output logic              b_rvalid_o,
  output logic [Width-1:0]  b_rdata_o,
  output logic [1:0]        b_rerror_o, // Bit1: Uncorrectable, Bit0: Correctable

  // config
  input [CfgW-1:0] cfg_i
);

  // Calculate ECC width
  localparam int ParWidth  = (EnableParity) ? 1 :
                             (!EnableECC)   ? 0 :
                             (Width <=   4) ? 4 :
                             (Width <=  11) ? 5 :
                             (Width <=  26) ? 6 :
                             (Width <=  57) ? 7 :
                             (Width <= 120) ? 8 : 8 ;
  localparam int TotalWidth = Width + ParWidth;

  logic                  a_req_q,    a_req_d ;
  logic                  a_write_q,  a_write_d ;
  logic [SramAw-1:0]     a_addr_q,   a_addr_d ;
  logic [TotalWidth-1:0] a_wdata_q,  a_wdata_d ;
  logic                  a_rvalid_q, a_rvalid_d, a_rvalid_sram ;
  logic [Width-1:0]      a_rdata_q,  a_rdata_d ;
  logic [TotalWidth-1:0] a_rdata_sram ;
  logic [1:0]            a_rerror_q, a_rerror_d ;

  logic                  b_req_q,    b_req_d ;
  logic                  b_write_q,  b_write_d ;
  logic [SramAw-1:0]     b_addr_q,   b_addr_d ;
  logic [TotalWidth-1:0] b_wdata_q,  b_wdata_d ;
  logic                  b_rvalid_q, b_rvalid_d, b_rvalid_sram ;
  logic [Width-1:0]      b_rdata_q,  b_rdata_d ;
  logic [TotalWidth-1:0] b_rdata_sram ;
  logic [1:0]            b_rerror_q, b_rerror_d ;

  if (MemT == "REGISTER") begin : gen_regmem
    prim_ram_2p #(
      .Width (TotalWidth),
      .Depth (Depth),
      // force register implementation for all targets
      .Impl(prim_pkg::ImplGeneric)
    ) u_mem (
      .clk_a_i    (clk_i),
      .clk_b_i    (clk_i),

      .a_req_i    (a_req_q),
      .a_write_i  (a_write_q),
      .a_addr_i   (a_addr_q),
      .a_wdata_i  (a_wdata_q),
      .a_rdata_o  (a_rdata_sram),

      .b_req_i    (b_req_q),
      .b_write_i  (b_write_q),
      .b_addr_i   (b_addr_q),
      .b_wdata_i  (b_wdata_q),
      .b_rdata_o  (b_rdata_sram)
    );
  // end else if (TotalWidth == aa && Depth == yy) begin
  end else if (MemT == "SRAM") begin : gen_srammem
    prim_ram_2p #(
      .Width (TotalWidth),
      .Depth (Depth)
    ) u_mem (
      .clk_a_i    (clk_i),
      .clk_b_i    (clk_i),

      .a_req_i    (a_req_q),
      .a_write_i  (a_write_q),
      .a_addr_i   (a_addr_q),
      .a_wdata_i  (a_wdata_q),
      .a_rdata_o  (a_rdata_sram),

      .b_req_i    (b_req_q),
      .b_write_i  (b_write_q),
      .b_addr_i   (b_addr_q),
      .b_wdata_i  (b_wdata_q),
      .b_rdata_o  (b_rdata_sram)
    );
  end

 always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
       a_rvalid_sram <= '0;
       b_rvalid_sram <= '0;
    end else begin
      a_rvalid_sram <= a_req_q & ~a_write_q;
      b_rvalid_sram <= b_req_q & ~b_write_q;
    end
  end

  assign a_req_d              = a_req_i;
  assign a_write_d            = a_write_i;
  assign a_addr_d             = a_addr_i;
  assign a_rvalid_o           = a_rvalid_q;
  assign a_rdata_o            = a_rdata_q;
  assign a_rerror_o           = a_rerror_q;

  assign b_req_d              = b_req_i;
  assign b_write_d            = b_write_i;
  assign b_addr_d             = b_addr_i;
  assign b_rvalid_o           = b_rvalid_q;
  assign b_rdata_o            = b_rdata_q;
  assign b_rerror_o           = b_rerror_q;

  // TODO: Parity Logic
  `ASSERT_INIT(ParityNotYetSupported_A, EnableParity == 0)

  if (EnableParity == 0 && EnableECC) begin : gen_secded

    // check supported widths
    `ASSERT_INIT(SecDecWidth_A, Width inside {32})

    if (Width == 32) begin : gen_secded_39_32
      prim_secded_39_32_enc u_enc_a (.in(a_wdata_i), .out(a_wdata_d));
      prim_secded_39_32_dec u_dec_a (
        .in         (a_rdata_sram),
        .d_o        (a_rdata_d),
        .syndrome_o (),
        .err_o      (a_rerror_d)
      );
      prim_secded_39_32_enc u_enc_b (.in(b_wdata_i), .out(b_wdata_d));
      prim_secded_39_32_dec u_dec_b (
        .in         (b_rdata_sram),
        .d_o        (b_rdata_d),
        .syndrome_o (),
        .err_o      (b_rerror_d)
      );
      assign a_rvalid_d = a_rvalid_sram;
      assign b_rvalid_d = b_rvalid_sram;
    end
  end else begin : gen_nosecded
    assign a_wdata_d[0+:Width] = a_wdata_i;
    assign b_wdata_d[0+:Width] = b_wdata_i;
    assign a_rdata_d  = a_rdata_sram;
    assign b_rdata_d  = b_rdata_sram;
    assign a_rvalid_d = a_rvalid_sram;
    assign b_rvalid_d = b_rvalid_sram;
    assign a_rerror_d = 2'b00;
    assign b_rerror_d = 2'b00;
  end

  if (EnableInputPipeline) begin : gen_regslice_input
    // Put the register slices between ECC encoding to SRAM port
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        a_req_q   <= '0;
        a_write_q <= '0;
        a_addr_q  <= '0;
        a_wdata_q <= '0;

        b_req_q   <= '0;
        b_write_q <= '0;
        b_addr_q  <= '0;
        b_wdata_q <= '0;
      end else begin
        a_req_q   <= a_req_d;
        a_write_q <= a_write_d;
        a_addr_q  <= a_addr_d;
        a_wdata_q <= a_wdata_d;

        b_req_q   <= b_req_d;
        b_write_q <= b_write_d;
        b_addr_q  <= b_addr_d;
        b_wdata_q <= b_wdata_d;
      end
    end
  end else begin : gen_dirconnect_input
    assign a_req_q   = a_req_d;
    assign a_write_q = a_write_d;
    assign a_addr_q  = a_addr_d;
    assign a_wdata_q = a_wdata_d;

    assign b_req_q   = b_req_d;
    assign b_write_q = b_write_d;
    assign b_addr_q  = b_addr_d;
    assign b_wdata_q = b_wdata_d;
  end

  if (EnableOutputPipeline) begin : gen_regslice_output
    // Put the register slices between ECC decoding to output
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        a_rvalid_q <= '0;
        a_rdata_q  <= '0;
        a_rerror_q <= '0;

        b_rvalid_q <= '0;
        b_rdata_q  <= '0;
        b_rerror_q <= '0;
      end else begin
        a_rvalid_q <= a_rvalid_d;
        a_rdata_q  <= a_rdata_d ;
        a_rerror_q <= a_rerror_d;

        b_rvalid_q <= b_rvalid_d;
        b_rdata_q  <= b_rdata_d ;
        b_rerror_q <= b_rerror_d;
      end
    end
  end else begin : gen_dirconnect_output
    assign a_rvalid_q = a_rvalid_d;
    assign a_rdata_q  = a_rdata_d;
    assign a_rerror_q = a_rerror_d;

    assign b_rvalid_q = b_rvalid_d;
    assign b_rdata_q  = b_rdata_d;
    assign b_rerror_q = b_rerror_d;
  end

endmodule
