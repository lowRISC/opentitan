// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module cheriot_tag_filter #(
  // The number of outstanding TL transaction the IP supports
  parameter int unsigned NumOutstanding = 32'd4
)(
  input clk_i,
  input rst_ni,

  // CHERIoT mode enabled
  input  prim_mubi_pkg::mubi4_t cheriot_ena_i,

  // Device port
  input  tlul_pkg::tl_h2d_t tl_d_i,
  input  logic              tag_d_i,
  output tlul_pkg::tl_d2h_t tl_d_o,
  output logic              tag_d_o,

  // Meta port
  output tlul_pkg::tl_h2d_t tl_m_o,
  output logic              tag_m_o,
  input  tlul_pkg::tl_d2h_t tl_m_i,
  input  logic              tag_m_i,

  // Host port
  output tlul_pkg::tl_h2d_t tl_h_o,
  input  tlul_pkg::tl_d2h_t tl_h_i
);

  ///////////
  // Types //
  ///////////

  // The meta data type handed between the host's request and response channel
  typedef struct packed {
    logic cap_store;
    logic cap;
    logic aligned;
  } req_rsp_meta_t;


  /////////////
  // Signals //
  /////////////

  // Request handshaking signals
  logic tl_d_req_ready;
  logic tl_m_req_valid;
  logic tl_h_req_valid;

  // Input port of the meta FIFO
  logic          meta_req_valid;
  logic          meta_req_ready;
  req_rsp_meta_t meta_req;

  // Output port of the meta FIFO
  logic          meta_rsp_valid;
  logic          meta_rsp_ready;
  req_rsp_meta_t meta_rsp;

  // Whether we need to lookup or fork into the meta memory
  logic require_lookup;
  // Whether we need to join a meta lookup
  logic require_join;

  // Response handshaking signals
  logic tl_d_rsp_valid;
  logic tl_h_rsp_ready;
  logic tl_m_rsp_ready;

  // Unused meta response signals
  logic unused_m_rsp;

  // Tag bit store. We only do the lookup on the lower word of a capability to safe
  // bandwidth into the meta memory. For the directly following meta word, we store
  // the capability
  logic tag_d_d, tag_d_q;

  logic tl_d_is_read;
  logic tl_d_is_write;
  logic tl_d_is_aligned;


  //////////
  // Fork //
  //////////

  assign tl_d_is_read    = tl_d_i.a_opcode == tlul_pkg::Get;
  assign tl_d_is_write   = tl_d_i.a_opcode == tlul_pkg::PutFullData ||
                           tl_d_i.a_opcode == tlul_pkg::PutPartialData;
  assign tl_d_is_aligned = !tl_d_i.a_address[2];

  // We need to perform a lookup on 64-bit-aligned reads where the host hints
  // us a valid capability load or on any write. A lookup is only required if CHERIoT is enabled.
  assign require_lookup = prim_mubi_pkg::mubi4_test_true_strict(cheriot_ena_i) ?
                          (tl_d_is_read   &&                                     // Read,
                          tl_d_is_aligned &&                                     // 64-bit-aligned,
                          tag_d_i)        ||                                     // hinted cap
                          tl_d_is_write                                        : // or write
                          1'b0;

  // We only fork the meta channel if a lookup is required
  stream_fork_dynamic #(
    .N_OUP(32'd3)
  ) u_stream_fork_dynamic (
    .clk_i,
    .rst_ni,
    .valid_i    ( tl_d_i.a_valid                                   ),
    .ready_o    ( tl_d_req_ready                                   ),
    .sel_i      ( {1'b1, require_lookup, 1'b1}                     ),
    .sel_valid_i( tl_d_i.a_valid                                   ),
    .sel_ready_o( /* NOT CONNECTED */                              ),
    .valid_o    ( {meta_req_valid, tl_m_req_valid, tl_h_req_valid} ),
    .ready_i    ( {meta_req_ready, tl_m_i.a_ready, tl_h_i.a_ready} )
  );


  ////////////////
  // Meta Store //
  ////////////////

  // Assemble meta data between host's request and response channel
  assign meta_req = '{
    cap:       tag_d_i,
    aligned:   tl_d_is_aligned,
    cap_store: tl_d_is_write
  };

  prim_fifo_sync #(
    .Width(32'd3),
    .Pass(1'b0),
    .Depth(NumOutstanding),
    .NeverClears(1'b1),
    .Secure(1'b1)
  ) u_prim_fifo_sync_align (
    .clk_i,
    .rst_ni,
    .clr_i   ( 1'b0           ),
    .wvalid_i( meta_req_valid ),
    .wready_o( meta_req_ready ),
    .wdata_i ( meta_req       ),
    .rvalid_o( meta_rsp_valid ),
    .rready_i( meta_rsp_ready ),
    .rdata_o ( meta_rsp       ),
    .full_o  (                ),
    .depth_o (                ),
    .err_o   (                )
  );


  //////////
  // Join //
  //////////

  // We need to join in the response from the meta SRAM if CHERIoT is enabled
  // Ibex hints capability reads thus a join is requested through the `meta_rsp.cap` signal.
  assign require_join = prim_mubi_pkg::mubi4_test_true_strict(cheriot_ena_i)     ?
                        meta_rsp.cap_store || (meta_rsp.cap && meta_rsp.aligned) :
                        1'b0;

  stream_join_dynamic #(
    .N_INP(32'd3)
  ) u_stream_join_dynamic (
    .inp_valid_i( {meta_rsp_valid, tl_m_i.d_valid, tl_h_i.d_valid} ),
    .inp_ready_o( {meta_rsp_ready, tl_m_rsp_ready, tl_h_rsp_ready} ),
    .sel_i      ( {1'b1, require_join, 1'b1} ),
    .oup_valid_o( tl_d_rsp_valid ),
    .oup_ready_i( tl_d_i.d_ready )
  );


  //////////////////////////
  // Stick Capability Tag //
  //////////////////////////

  assign tag_m_o = tag_d_i;

  always_comb begin: proc_sticky_tag_d_o
    tag_d_d = tag_d_q;
    tag_d_o = tag_d_q;
    if(tl_d_o.d_valid && tl_d_i.d_ready) begin
      if(meta_rsp.aligned) begin
        tag_d_o = tag_m_i;
        tag_d_d = tag_m_i;
      end else begin
        tag_d_d = 1'b0;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_store_r_cap_tag
    if(!rst_ni) begin
      tag_d_q <= 1'b0;
    end else begin
      tag_d_q <= tag_d_d;
    end
  end


  ////////////////////
  // TL connections //
  ////////////////////

  // We forward the host requests to both endpoints
  always_comb begin: proc_connect_tl_req
    tl_h_o         = tl_d_i;
    tl_h_o.a_valid = tl_h_req_valid;
    tl_h_o.d_ready = tl_h_rsp_ready;

    tl_m_o         = tl_d_i;
    tl_m_o.a_valid = tl_m_req_valid;
    tl_m_o.d_ready = tl_m_rsp_ready;
  end

  // We disregard all of the meta SRAM response except for the tag bit and the error bit
  always_comb begin: proc_connect_tl_rsp
    tl_d_o         = tl_h_i;
    tl_d_o.d_error = tl_d_o.d_error || tl_m_i.d_error;
    tl_d_o.a_ready = tl_d_req_ready;
    tl_d_o.d_valid = tl_d_rsp_valid;
  end

  // The response and data integrity is not checked, as both the RMW and the tag filter are
  // lock-stepped.
  assign unused_m_rsp = ^{tl_m_i.d_data,
                          tl_m_i.d_opcode,
                          tl_m_i.d_param,
                          tl_m_i.d_sink,
                          tl_m_i.d_size,
                          tl_m_i.d_source,
                          tl_m_i.d_user
                        };

  ////////////////
  // Assertions //
  ////////////////

  // Meta FIFO has to be valid when device port handshakes its response
  `ASSERT(MetaRspValidOnDHs_A, (tl_d_o.d_valid && tl_d_i.d_ready) |-> meta_rsp_valid)

endmodule
