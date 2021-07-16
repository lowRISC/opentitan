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
  parameter int OutWidth = 32
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

  prim_packer_fifo #(
    .InW(edn_pkg::ENDPOINT_BUS_WIDTH),
    .OutW(OutWidth)
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

endmodule : prim_edn_req
