// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Example memory mapped timer
module timer #(
  // Bus data width (must be 32)
  parameter int unsigned DataWidth    = 32,
  // Bus address width
  parameter int unsigned AddressWidth = 32
) (
  input  logic                    clk_i,
  input  logic                    rst_ni,
  // Bus interface
  input  logic                    timer_req_i,

  input  logic [AddressWidth-1:0] timer_addr_i,
  input  logic                    timer_we_i,
  input  logic [ DataWidth/8-1:0] timer_be_i,
  input  logic [   DataWidth-1:0] timer_wdata_i,
  output logic                    timer_rvalid_o,
  output logic [   DataWidth-1:0] timer_rdata_o,
  output logic                    timer_err_o,
  output logic                    timer_intr_o
);

  // The timers are always 64 bits
  localparam int unsigned TW = 64;
  // Upper bits of address are decoded into timer_req_i
  localparam int unsigned ADDR_OFFSET = 10; // 1kB
  // Register map
  localparam bit [9:0] MTIME_LOW = 0;
  localparam bit [9:0] MTIME_HIGH = 4;
  localparam bit [9:0] MTIMECMP_LOW = 8;
  localparam bit [9:0] MTIMECMP_HIGH = 12;

  logic                 timer_we;
  logic                 mtime_we, mtimeh_we;
  logic                 mtimecmp_we, mtimcmph_we;
  logic [DataWidth-1:0] mtime_wdata, mtimeh_wdata;
  logic [DataWidth-1:0] mtimecmp_wdata, mtimecmph_wdata;
  logic [TW-1:0]        mtime_q, mtime_d, mtime_inc;
  logic [TW-1:0]        mtimecmp_q, mtimecmp_d;
  logic                 interrupt_q, interrupt_d;
  logic                 error_q, error_d;
  logic [DataWidth-1:0] rdata_q, rdata_d;
  logic                 rvalid_q;

  // Global write enable for all registers
  assign timer_we = timer_req_i & timer_we_i;

  // mtime increments every cycle
  assign mtime_inc = mtime_q + 64'b1;

  // Generate write data based on byte strobes
  for (genvar b = 0; b < DataWidth / 8; b++) begin : gen_byte_wdata

    assign mtime_wdata[(b*8)+:8]     = timer_be_i[b] ? timer_wdata_i[b*8+:8] :
                                                       mtime_q[(b*8)+:8];
    assign mtimeh_wdata[(b*8)+:8]    = timer_be_i[b] ? timer_wdata_i[b*8+:8] :
                                                       mtime_q[DataWidth+(b*8)+:8];
    assign mtimecmp_wdata[(b*8)+:8]  = timer_be_i[b] ? timer_wdata_i[b*8+:8] :
                                                       mtimecmp_q[(b*8)+:8];
    assign mtimecmph_wdata[(b*8)+:8] = timer_be_i[b] ? timer_wdata_i[b*8+:8] :
                                                       mtimecmp_q[DataWidth+(b*8)+:8];
  end

  // Generate write enables
  assign mtime_we     = timer_we & (timer_addr_i[ADDR_OFFSET-1:0] == MTIME_LOW);
  assign mtimeh_we    = timer_we & (timer_addr_i[ADDR_OFFSET-1:0] == MTIME_HIGH);
  assign mtimecmp_we  = timer_we & (timer_addr_i[ADDR_OFFSET-1:0] == MTIMECMP_LOW);
  assign mtimecmph_we = timer_we & (timer_addr_i[ADDR_OFFSET-1:0] == MTIMECMP_HIGH);

  // Generate next data
  assign mtime_d    = {(mtimeh_we    ? mtimeh_wdata    : mtime_inc[63:32]),
                       (mtime_we     ? mtime_wdata     : mtime_inc[31:0])};
  assign mtimecmp_d = {(mtimecmph_we ? mtimecmph_wdata : mtimecmp_q[63:32]),
                       (mtimecmp_we  ? mtimecmp_wdata  : mtimecmp_q[31:0])};

  // Generate registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      mtime_q <= 'b0;
    end else begin
      mtime_q <= mtime_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      mtimecmp_q <= 'b0;
    end else if (mtimecmp_we | mtimecmph_we) begin
      mtimecmp_q <= mtimecmp_d;
    end
  end

  // interrupt remains set until mtimecmp is written
  assign interrupt_d  = ((mtime_q >= mtimecmp_q) | interrupt_q) & ~(mtimecmp_we | mtimecmph_we);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      interrupt_q <= 'b0;
    end else begin
      interrupt_q <= interrupt_d;
    end
  end

  assign timer_intr_o = interrupt_q;

  // Read data
  always_comb begin
    rdata_d = 'b0;
    error_d = 1'b0;
    unique case (timer_addr_i[ADDR_OFFSET-1:0])
      MTIME_LOW:     rdata_d = mtime_q[31:0];
      MTIME_HIGH:    rdata_d = mtime_q[63:32];
      MTIMECMP_LOW:  rdata_d = mtimecmp_q[31:0];
      MTIMECMP_HIGH: rdata_d = mtimecmp_q[63:32];
      default: begin
        rdata_d = 'b0;
        // Error if no address matched
        error_d = 1'b1;
      end
    endcase
  end

  // error_q and rdata_q are only valid when rvalid_q is high
  always_ff @(posedge clk_i) begin
    if (timer_req_i) begin
      rdata_q <= rdata_d;
      error_q <= error_d;
    end
  end

  assign timer_rdata_o = rdata_q;

  // Read data is always valid one cycle after a request
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvalid_q <= 1'b0;
    end else begin
      rvalid_q <= timer_req_i;
    end
  end

  assign timer_rvalid_o = rvalid_q;
  assign timer_err_o    = error_q;

  // Assertions
  `ASSERT_INIT(param_legal, DataWidth == 32)
endmodule
