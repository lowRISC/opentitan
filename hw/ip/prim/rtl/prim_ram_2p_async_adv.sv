// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Asynchronous Dual-Port SRAM Wrapper
//
// Supported configurations:
// - ECC for 32b and 64b wide memories with no write mask
//   (Width == 32 or Width == 64, DataBitsPerMask is ignored).
// - Byte parity if Width is a multiple of 8 bit and write masks have Byte
//   granularity (DataBitsPerMask == 8).
//
// Note that the write mask needs to be per Byte if parity is enabled. If ECC is enabled, the write
// mask cannot be used and has to be tied to {Width{1'b1}}.

`include "prim_assert.sv"

module prim_ram_2p_async_adv import prim_ram_2p_pkg::*; #(
  parameter  int Depth                = 512,
  parameter  int Width                = 32,
  parameter  int DataBitsPerMask      = 1,  // Number of data bits per bit of write mask
  parameter      MemInitFile          = "", // VMEM file to initialize the memory with

  // Configurations
  parameter  bit EnableECC            = 0, // Enables per-word ECC
  parameter  bit EnableParity         = 0, // Enables per-Byte Parity
  parameter  bit EnableInputPipeline  = 0, // Adds an input register (read latency +1)
  parameter  bit EnableOutputPipeline = 0, // Adds an output register (read latency +1)

  // This switch allows to switch to standard Hamming ECC instead of the HSIAO ECC.
  // It is recommended to leave this parameter at its default setting (HSIAO),
  // since this results in a more compact and faster implementation.
  parameter bit HammingECC            = 0,

  localparam int Aw                   = prim_util_pkg::vbits(Depth)
) (
  input clk_a_i,
  input clk_b_i,
  input rst_a_ni,
  input rst_b_ni,

  input                    a_req_i,
  input                    a_write_i,
  input        [Aw-1:0]    a_addr_i,
  input        [Width-1:0] a_wdata_i,
  input        [Width-1:0] a_wmask_i,  // cannot be used with ECC, tie to 1 in that case
  output logic [Width-1:0] a_rdata_o,
  output logic             a_rvalid_o, // read response (a_rdata_o) is valid
  output logic [1:0]       a_rerror_o, // Bit1: Uncorrectable, Bit0: Correctable

  input                    b_req_i,
  input                    b_write_i,
  input        [Aw-1:0]    b_addr_i,
  input        [Width-1:0] b_wdata_i,
  input        [Width-1:0] b_wmask_i,  // cannot be used with ECC, tie to 1 in that case
  output logic [Width-1:0] b_rdata_o,
  output logic             b_rvalid_o, // read response (b_rdata_o) is valid
  output logic [1:0]       b_rerror_o, // Bit1: Uncorrectable, Bit0: Correctable

  // config
  input ram_2p_cfg_t       cfg_i
);


  `ASSERT_INIT(CannotHaveEccAndParity_A, !(EnableParity && EnableECC))

  // Calculate ECC width
  localparam int ParWidth  = (EnableParity) ? Width/8 :
                             (!EnableECC)   ? 0 :
                             (Width <=   4) ? 4 :
                             (Width <=  11) ? 5 :
                             (Width <=  26) ? 6 :
                             (Width <=  57) ? 7 :
                             (Width <= 120) ? 8 : 8 ;
  localparam int TotalWidth = Width + ParWidth;

  // If byte parity is enabled, the write enable bits are used to write memory colums
  // with 8 + 1 = 9 bit width (data plus corresponding parity bit).
  // If ECC is enabled, the DataBitsPerMask is ignored.
  localparam int LocalDataBitsPerMask = (EnableParity) ? 9          :
                                        (EnableECC)    ? TotalWidth :
                                                         DataBitsPerMask;

  ////////////////////////////
  // RAM Primitive Instance //
  ////////////////////////////

  logic                    a_req_q,    a_req_d ;
  logic                    a_write_q,  a_write_d ;
  logic [Aw-1:0]           a_addr_q,   a_addr_d ;
  logic [TotalWidth-1:0]   a_wdata_q,  a_wdata_d ;
  logic [TotalWidth-1:0]   a_wmask_q,  a_wmask_d ;
  logic                    a_rvalid_q, a_rvalid_d, a_rvalid_sram_q ;
  logic [Width-1:0]        a_rdata_q,  a_rdata_d ;
  logic [TotalWidth-1:0]   a_rdata_sram ;
  logic [1:0]              a_rerror_q, a_rerror_d ;

  logic                    b_req_q,    b_req_d ;
  logic                    b_write_q,  b_write_d ;
  logic [Aw-1:0]           b_addr_q,   b_addr_d ;
  logic [TotalWidth-1:0]   b_wdata_q,  b_wdata_d ;
  logic [TotalWidth-1:0]   b_wmask_q,  b_wmask_d ;
  logic                    b_rvalid_q, b_rvalid_d, b_rvalid_sram_q ;
  logic [Width-1:0]        b_rdata_q,  b_rdata_d ;
  logic [TotalWidth-1:0]   b_rdata_sram ;
  logic [1:0]              b_rerror_q, b_rerror_d ;

  prim_ram_2p #(
    .MemInitFile     (MemInitFile),

    .Width           (TotalWidth),
    .Depth           (Depth),
    .DataBitsPerMask (LocalDataBitsPerMask)
  ) u_mem (
    .clk_a_i    (clk_a_i),
    .clk_b_i    (clk_b_i),

    .a_req_i    (a_req_q),
    .a_write_i  (a_write_q),
    .a_addr_i   (a_addr_q),
    .a_wdata_i  (a_wdata_q),
    .a_wmask_i  (a_wmask_q),
    .a_rdata_o  (a_rdata_sram),

    .b_req_i    (b_req_q),
    .b_write_i  (b_write_q),
    .b_addr_i   (b_addr_q),
    .b_wdata_i  (b_wdata_q),
    .b_wmask_i  (b_wmask_q),
    .b_rdata_o  (b_rdata_sram),

    .cfg_i
  );

  always_ff @(posedge clk_a_i or negedge rst_a_ni) begin
    if (!rst_a_ni) begin
      a_rvalid_sram_q <= 1'b0;
    end else begin
      a_rvalid_sram_q <= a_req_q & ~a_write_q;
    end
  end
  always_ff @(posedge clk_b_i or negedge rst_b_ni) begin
    if (!rst_b_ni) begin
      b_rvalid_sram_q <= 1'b0;
    end else begin
      b_rvalid_sram_q <= b_req_q & ~b_write_q;
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

  /////////////////////////////
  // ECC / Parity Generation //
  /////////////////////////////

  if (EnableParity == 0 && EnableECC) begin : gen_secded

    // check supported widths
    `ASSERT_INIT(SecDecWidth_A, Width inside {32})

    // the wmask is constantly set to 1 in this case
    `ASSERT(OnlyWordWritePossibleWithEccPortA_A, a_req_i |->
        a_wmask_i == {Width{1'b1}}, clk_a_i, rst_a_ni)
    `ASSERT(OnlyWordWritePossibleWithEccPortB_A, b_req_i |->
        b_wmask_i == {Width{1'b1}}, clk_b_i, rst_b_ni)

    assign a_wmask_d = {TotalWidth{1'b1}};
    assign b_wmask_d = {TotalWidth{1'b1}};

    if (Width == 32) begin : gen_secded_39_32
      if (HammingECC) begin : gen_hamming
        prim_secded_hamming_39_32_enc u_enc_a (
          .in(a_wdata_i),
          .out(a_wdata_d)
        );
        prim_secded_hamming_39_32_dec u_dec_a (
          .in         (a_rdata_sram),
          .d_o        (a_rdata_d[0+:Width]),
          .syndrome_o ( ),
          .err_o      (a_rerror_d)
        );
        prim_secded_hamming_39_32_enc u_enc_b (
          .in(b_wdata_i),
          .out(b_wdata_d)
        );
        prim_secded_hamming_39_32_dec u_dec_b (
          .in         (b_rdata_sram),
          .d_o        (b_rdata_d[0+:Width]),
          .syndrome_o ( ),
          .err_o      (b_rerror_d)
        );
      end else begin : gen_hsiao
        prim_secded_39_32_enc u_enc_a (
          .in(a_wdata_i),
          .out(a_wdata_d)
        );
        prim_secded_39_32_dec u_dec_a (
          .in         (a_rdata_sram),
          .d_o        (a_rdata_d[0+:Width]),
          .syndrome_o ( ),
          .err_o      (a_rerror_d)
        );
        prim_secded_39_32_enc u_enc_b (
          .in(b_wdata_i),
          .out(b_wdata_d)
        );
        prim_secded_39_32_dec u_dec_b (
          .in         (b_rdata_sram),
          .d_o        (b_rdata_d[0+:Width]),
          .syndrome_o ( ),
          .err_o      (b_rerror_d)
        );
      end
    end
  end else if (EnableParity) begin : gen_byte_parity

    `ASSERT_INIT(ParityNeedsByteWriteMask_A, DataBitsPerMask == 8)
    `ASSERT_INIT(WidthNeedsToBeByteAligned_A, Width % 8 == 0)

    always_comb begin : p_parity
      a_rerror_d = '0;
      b_rerror_d = '0;
      for (int i = 0; i < Width/8; i ++) begin
        // Data mapping. We have to make 8+1 = 9 bit groups
        // that have the same write enable such that FPGA tools
        // can map this correctly to BRAM resources.
        a_wmask_d[i*9 +: 8] = a_wmask_i[i*8 +: 8];
        a_wdata_d[i*9 +: 8] = a_wdata_i[i*8 +: 8];
        a_rdata_d[i*8 +: 8] = a_rdata_sram[i*9 +: 8];
        b_wmask_d[i*9 +: 8] = b_wmask_i[i*8 +: 8];
        b_wdata_d[i*9 +: 8] = b_wdata_i[i*8 +: 8];
        b_rdata_d[i*8 +: 8] = b_rdata_sram[i*9 +: 8];

        // parity generation (odd parity)
        a_wdata_d[i*9 + 8] = ~(^a_wdata_i[i*8 +: 8]);
        a_wmask_d[i*9 + 8] = &a_wmask_i[i*8 +: 8];
        b_wdata_d[i*9 + 8] = ~(^b_wdata_i[i*8 +: 8]);
        b_wmask_d[i*9 + 8] = &b_wmask_i[i*8 +: 8];
        // parity decoding (errors are always uncorrectable)
        a_rerror_d[1] |= ~(^{a_rdata_sram[i*9 +: 8], a_rdata_sram[i*9 + 8]});
        b_rerror_d[1] |= ~(^{b_rdata_sram[i*9 +: 8], b_rdata_sram[i*9 + 8]});
      end
    end
  end else begin : gen_nosecded_noparity
    assign a_wmask_d  = a_wmask_i;
    assign b_wmask_d  = b_wmask_i;
    assign a_wdata_d  = a_wdata_i;
    assign b_wdata_d  = b_wdata_i;
    assign a_rdata_d  = a_rdata_sram[0+:Width];
    assign b_rdata_d  = b_rdata_sram[0+:Width];
    assign a_rerror_d = '0;
    assign b_rerror_d = '0;
  end

  assign a_rvalid_d = a_rvalid_sram_q;
  assign b_rvalid_d = b_rvalid_sram_q;

  /////////////////////////////////////
  // Input/Output Pipeline Registers //
  /////////////////////////////////////

  if (EnableInputPipeline) begin : gen_regslice_input
    // Put the register slices between ECC encoding to SRAM port
    always_ff @(posedge clk_a_i or negedge rst_a_ni) begin
      if (!rst_a_ni) begin
        a_req_q   <= '0;
        a_write_q <= '0;
        a_addr_q  <= '0;
        a_wdata_q <= '0;
        a_wmask_q <= '0;
      end else begin
        a_req_q   <= a_req_d;
        a_write_q <= a_write_d;
        a_addr_q  <= a_addr_d;
        a_wdata_q <= a_wdata_d;
        a_wmask_q <= a_wmask_d;
      end
    end
    always_ff @(posedge clk_b_i or negedge rst_b_ni) begin
      if (!rst_b_ni) begin
        b_req_q   <= '0;
        b_write_q <= '0;
        b_addr_q  <= '0;
        b_wdata_q <= '0;
        b_wmask_q <= '0;
      end else begin
        b_req_q   <= b_req_d;
        b_write_q <= b_write_d;
        b_addr_q  <= b_addr_d;
        b_wdata_q <= b_wdata_d;
        b_wmask_q <= b_wmask_d;
      end
    end
  end else begin : gen_dirconnect_input
    assign a_req_q   = a_req_d;
    assign a_write_q = a_write_d;
    assign a_addr_q  = a_addr_d;
    assign a_wdata_q = a_wdata_d;
    assign a_wmask_q = a_wmask_d;

    assign b_req_q   = b_req_d;
    assign b_write_q = b_write_d;
    assign b_addr_q  = b_addr_d;
    assign b_wdata_q = b_wdata_d;
    assign b_wmask_q = b_wmask_d;
  end

  if (EnableOutputPipeline) begin : gen_regslice_output
    // Put the register slices between ECC decoding to output
    always_ff @(posedge clk_a_i or negedge rst_a_ni) begin
      if (!rst_a_ni) begin
        a_rvalid_q <= '0;
        a_rdata_q  <= '0;
        a_rerror_q <= '0;
      end else begin
        a_rvalid_q <= a_rvalid_d;
        a_rdata_q  <= a_rdata_d;
        // tie to zero if the read data is not valid
        a_rerror_q <= a_rerror_d & {2{a_rvalid_d}};
      end
    end
    always_ff @(posedge clk_b_i or negedge rst_b_ni) begin
      if (!rst_b_ni) begin
        b_rvalid_q <= '0;
        b_rdata_q  <= '0;
        b_rerror_q <= '0;
      end else begin
        b_rvalid_q <= b_rvalid_d;
        b_rdata_q  <= b_rdata_d;
        // tie to zero if the read data is not valid
        b_rerror_q <= b_rerror_d & {2{b_rvalid_d}};
      end
    end
  end else begin : gen_dirconnect_output
    assign a_rvalid_q = a_rvalid_d;
    assign a_rdata_q  = a_rdata_d;
    // tie to zero if the read data is not valid
    assign a_rerror_q = a_rerror_d & {2{a_rvalid_d}};

    assign b_rvalid_q = b_rvalid_d;
    assign b_rdata_q  = b_rdata_d;
    // tie to zero if the read data is not valid
    assign b_rerror_q = b_rerror_d & {2{b_rvalid_d}};
  end

endmodule : prim_ram_2p_async_adv
