// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Single-Port SRAM Wrapper
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

module prim_ram_1p_adv import prim_ram_1p_pkg::*; #(
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
  input clk_i,
  input rst_ni,

  input                      req_i,
  input                      write_i,
  input        [Aw-1:0]      addr_i,
  input        [Width-1:0]   wdata_i,
  input        [Width-1:0]   wmask_i,
  output logic [Width-1:0]   rdata_o,
  output logic               rvalid_o, // read response (rdata_o) is valid
  output logic [1:0]         rerror_o, // Bit1: Uncorrectable, Bit0: Correctable

  // config
  input ram_1p_cfg_t         cfg_i
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

  logic                    req_q,    req_d ;
  logic                    write_q,  write_d ;
  logic [Aw-1:0]           addr_q,   addr_d ;
  logic [TotalWidth-1:0]   wdata_q,  wdata_d ;
  logic [TotalWidth-1:0]   wmask_q,  wmask_d ;
  logic                    rvalid_q, rvalid_d, rvalid_sram_q ;
  logic [Width-1:0]        rdata_q,  rdata_d ;
  logic [TotalWidth-1:0]   rdata_sram ;
  logic [1:0]              rerror_q, rerror_d ;

  prim_ram_1p #(
    .MemInitFile     (MemInitFile),

    .Width           (TotalWidth),
    .Depth           (Depth),
    .DataBitsPerMask (LocalDataBitsPerMask)
  ) u_mem (
    .clk_i,

    .req_i    (req_q),
    .write_i  (write_q),
    .addr_i   (addr_q),
    .wdata_i  (wdata_q),
    .wmask_i  (wmask_q),
    .rdata_o  (rdata_sram),
    .cfg_i
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvalid_sram_q <= 1'b0;
    end else begin
      rvalid_sram_q <= req_q & ~write_q;
    end
  end

  assign req_d              = req_i;
  assign write_d            = write_i;
  assign addr_d             = addr_i;
  assign rvalid_o           = rvalid_q;
  assign rdata_o            = rdata_q;
  assign rerror_o           = rerror_q;

  /////////////////////////////
  // ECC / Parity Generation //
  /////////////////////////////

  if (EnableParity == 0 && EnableECC) begin : gen_secded
    logic unused_wmask;
    assign unused_wmask = ^wmask_i;

    // check supported widths
    `ASSERT_INIT(SecDecWidth_A, Width inside {16, 32})

    // the wmask is constantly set to 1 in this case
    `ASSERT(OnlyWordWritePossibleWithEccPortA_A, req_i |->
          wmask_i == {Width{1'b1}})

    assign wmask_d = {TotalWidth{1'b1}};

    if (Width == 16) begin : gen_secded_22_16
      if (HammingECC) begin : gen_hamming
        prim_secded_hamming_22_16_enc u_enc (
          .data_i(wdata_i),
          .data_o(wdata_d)
        );
        prim_secded_hamming_22_16_dec u_dec (
          .data_i     (rdata_sram),
          .data_o     (rdata_d[0+:Width]),
          .syndrome_o ( ),
          .err_o      (rerror_d)
        );
      end else begin : gen_hsiao
        prim_secded_22_16_enc u_enc (
          .data_i(wdata_i),
          .data_o(wdata_d)
        );
        prim_secded_22_16_dec u_dec (
          .data_i     (rdata_sram),
          .data_o     (rdata_d[0+:Width]),
          .syndrome_o ( ),
          .err_o      (rerror_d)
        );
      end
    end else if (Width == 32) begin : gen_secded_39_32
      if (HammingECC) begin : gen_hamming
        prim_secded_hamming_39_32_enc u_enc (
          .data_i(wdata_i),
          .data_o(wdata_d)
        );
        prim_secded_hamming_39_32_dec u_dec (
          .data_i     (rdata_sram),
          .data_o     (rdata_d[0+:Width]),
          .syndrome_o ( ),
          .err_o      (rerror_d)
        );
      end else begin : gen_hsiao
        prim_secded_39_32_enc u_enc (
          .data_i(wdata_i),
          .data_o(wdata_d)
        );
        prim_secded_39_32_dec u_dec (
          .data_i     (rdata_sram),
          .data_o     (rdata_d[0+:Width]),
          .syndrome_o ( ),
          .err_o      (rerror_d)
        );
      end
    end

  end else if (EnableParity) begin : gen_byte_parity

    `ASSERT_INIT(WidthNeedsToBeByteAligned_A, Width % 8 == 0)
    `ASSERT_INIT(ParityNeedsByteWriteMask_A, DataBitsPerMask == 8)

    always_comb begin : p_parity
      rerror_d = '0;
      for (int i = 0; i < Width/8; i ++) begin
        // Data mapping. We have to make 8+1 = 9 bit groups
        // that have the same write enable such that FPGA tools
        // can map this correctly to BRAM resources.
        wmask_d[i*9 +: 8] = wmask_i[i*8 +: 8];
        wdata_d[i*9 +: 8] = wdata_i[i*8 +: 8];
        rdata_d[i*8 +: 8] = rdata_sram[i*9 +: 8];

        // parity generation (odd parity)
        wdata_d[i*9 + 8] = ~(^wdata_i[i*8 +: 8]);
        wmask_d[i*9 + 8] = &wmask_i[i*8 +: 8];
        // parity decoding (errors are always uncorrectable)
        rerror_d[1] |= ~(^{rdata_sram[i*9 +: 8], rdata_sram[i*9 + 8]});
      end
    end
  end else begin : gen_nosecded_noparity
    assign wmask_d = wmask_i;
    assign wdata_d = wdata_i;

    assign rdata_d  = rdata_sram[0+:Width];
    assign rerror_d = '0;
  end

  assign rvalid_d = rvalid_sram_q;

  /////////////////////////////////////
  // Input/Output Pipeline Registers //
  /////////////////////////////////////

  if (EnableInputPipeline) begin : gen_regslice_input
    // Put the register slices between ECC encoding to SRAM port
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        req_q   <= '0;
        write_q <= '0;
        addr_q  <= '0;
        wdata_q <= '0;
        wmask_q <= '0;
      end else begin
        req_q   <= req_d;
        write_q <= write_d;
        addr_q  <= addr_d;
        wdata_q <= wdata_d;
        wmask_q <= wmask_d;
      end
    end
  end else begin : gen_dirconnect_input
    assign req_q   = req_d;
    assign write_q = write_d;
    assign addr_q  = addr_d;
    assign wdata_q = wdata_d;
    assign wmask_q = wmask_d;
  end

  if (EnableOutputPipeline) begin : gen_regslice_output
    // Put the register slices between ECC decoding to output
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rvalid_q <= '0;
        rdata_q  <= '0;
        rerror_q <= '0;
      end else begin
        rvalid_q <= rvalid_d;
        rdata_q  <= rdata_d;
        // tie to zero if the read data is not valid
        rerror_q <= rerror_d & {2{rvalid_d}};
      end
    end
  end else begin : gen_dirconnect_output
    assign rvalid_q = rvalid_d;
    assign rdata_q  = rdata_d;
    // tie to zero if the read data is not valid
    assign rerror_q = rerror_d & {2{rvalid_d}};
  end

endmodule : prim_ram_1p_adv
