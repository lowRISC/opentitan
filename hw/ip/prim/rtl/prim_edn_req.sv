// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module can be used as a "gadget" to adapt the native 32bit width of the EDN network
// locally to the width needed by the consuming logic. For example, if the local consumer
// needs 128bit, this module would request four 32 bit words from EDN and stack them accordingly.
//
// The module also uses a req/ack synchronizer to synchronize the EDN data over to the local
// clock domain. Note that this assumes that the EDN data bus remains stable between subsequent
// requests.
//

`include "prim_assert.sv"

module prim_edn_req
  import prim_alert_pkg::*;
#(
  parameter int OutWidth = 32,
  // Repetition check for incoming edn data
  parameter bit RepCheck = 0,

  // EDN Request latency checker
  //
  //  Each consumer IP may have the maximum expected latency. MaxLatency
  //  parameter describes the expected latency in terms of the consumer clock
  //  cycles. If the edn request comes later than that, the assertion will be
  //  fired.
  //
  //  The default value is 0, which disables the assertion.
  parameter int unsigned MaxLatency = 0
) (
  // Design side
  input                       clk_i,
  input                       rst_ni,
  input                       req_chk_i, // Used for gating assertions. Drive to 1 during normal
                                         // operation.
  input                       req_i,
  output logic                ack_o,
  output logic [OutWidth-1:0] data_o,
  output logic                fips_o,
  output logic                err_o,  // current data_o failed repetition check
  // EDN side
  input                       clk_edn_i,
  input                       rst_edn_ni,
  output edn_pkg::edn_req_t   edn_o,
  input  edn_pkg::edn_rsp_t   edn_i
);

  // Stop requesting words from EDN once desired amount of data is available.
  logic word_req, word_ack;
  assign word_req = req_i & ~ack_o;

  logic [edn_pkg::ENDPOINT_BUS_WIDTH-1:0] word_data;
  logic word_fips;
  localparam int SyncWidth = $bits({edn_i.edn_fips, edn_i.edn_bus});
  prim_sync_reqack_data #(
    .Width(SyncWidth),
    .DataSrc2Dst(1'b0),
    .DataReg(1'b0)
  ) u_prim_sync_reqack_data (
    .clk_src_i  ( clk_i                           ),
    .rst_src_ni ( rst_ni                          ),
    .clk_dst_i  ( clk_edn_i                       ),
    .rst_dst_ni ( rst_edn_ni                      ),
    .req_chk_i  ( req_chk_i                       ),
    .src_req_i  ( word_req                        ),
    .src_ack_o  ( word_ack                        ),
    .dst_req_o  ( edn_o.edn_req                   ),
    .dst_ack_i  ( edn_i.edn_ack                   ),
    .data_i     ( {edn_i.edn_fips, edn_i.edn_bus} ),
    .data_o     ( {word_fips,      word_data}     )
  );

  if (RepCheck) begin : gen_rep_chk
    logic [edn_pkg::ENDPOINT_BUS_WIDTH-1:0] word_data_q;
    always_ff @(posedge clk_i) begin
      if (word_ack) begin
        word_data_q <= word_data;
      end
    end

    // do not check until we have received at least the first entry
    logic chk_rep;
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        chk_rep <= '0;
      end else if (word_ack) begin
        chk_rep <= 1'b1;
      end
    end

    // Need to track if any of the packed words has failed the repetition check, i.e., is identical
    // to the last packed word.
    logic err_d, err_q;
    assign err_d = (req_i && ack_o)                                  ? 1'b0 : // clear
                   (chk_rep && word_ack && word_data == word_data_q) ? 1'b1 : // set
                                                                       err_q; // keep
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        err_q <= 1'b0;
      end else begin
        err_q <= err_d;
      end
    end
    assign err_o = err_q;

  end else begin : gen_no_rep_chk // block: gen_rep_chk
    assign err_o = '0;
  end

  prim_packer_fifo #(
    .InW(edn_pkg::ENDPOINT_BUS_WIDTH),
    .OutW(OutWidth),
    .ClearOnRead(1'b0)
  ) u_prim_packer_fifo (
    .clk_i,
    .rst_ni,
    .clr_i    ( 1'b0          ), // not needed
    .wvalid_i ( word_ack      ),
    .wdata_i  ( word_data     ),
    // no need for backpressure since we're always ready to
    // sink data at this point.
    .wready_o (               ),
    .rvalid_o ( ack_o         ),
    .rdata_o  ( data_o        ),
    // we're always ready to receive the packed output word
    // at this point.
    .rready_i ( 1'b1          ),
    .depth_o  (               )
  );

  // Need to track if any of the packed words has been generated with a pre-FIPS seed, i.e., has
  // fips == 1'b0.
  logic fips_d, fips_q;
  assign fips_d = (req_i && ack_o) ? 1'b1               : // clear
                  (word_ack)       ? fips_q & word_fips : // accumulate
                                     fips_q;              // keep
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fips_q <= 1'b1;
    end else begin
      fips_q <= fips_d;
    end
  end
  assign fips_o = fips_q;

  ////////////////
  // Assertions //
  ////////////////

  // EDN Max Latency Checker
`ifndef SYNTHESIS
  if (MaxLatency != 0) begin: g_maxlatency_assertion
    localparam int unsigned LatencyW = $clog2(MaxLatency+1);
    logic [LatencyW-1:0] latency_counter;
    logic reset_counter;
    logic enable_counter;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) latency_counter <= '0;
      else if (reset_counter) latency_counter <= '0;
      else if (enable_counter) latency_counter <= latency_counter + 1'b1;
    end

    assign reset_counter  = ack_o;
    assign enable_counter = req_i;

    `ASSERT(MaxLatency_A, latency_counter <= MaxLatency)

    // TODO: Is it worth to check req & ack pair?
    //         _________________________________
    // req  __/                                 \______
    //                                           ____
    // ack  ____________________________________/    \_
    //
    //                                          | error

  end // g_maxlatency_assertion
`else // SYNTHESIS
  logic unused_param_maxlatency;
  assign unused_param_maxlatency = ^MaxLatency;
`endif // SYNTHESIS

endmodule : prim_edn_req
