// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TL-UL wrapper of the TRVK revocation filter (`cheriot_trvk_core`).
// Assumes a tagged capability load always arrives downstream as exactly two consecutive,
// uninterrupted 32-bit responses from a single, in-order requester.
module cheriot_trvk_tlul #(
  // The number of outstanding TL transaction the IP supports
  parameter int unsigned NumOutstanding     = 32'd4,
  // The width of the meta memory byte address space used to store the revocation bits
  parameter int unsigned RevBitmapAddrWidth = 32'd11,
  // The size of the revocation bitmap in bytes; bases beyond it have no revocation bit
  parameter int unsigned RevBitmapSizeBytes = 32'd1 << RevBitmapAddrWidth,
  // The base byte address of the meta SRAM holding the revocation bitmap
  parameter int unsigned RevBitmapBaseAddr  = 32'h0000_0000,
  // Enable ECC checking on the revocation bitmap memory data
  parameter bit          MemECC             = 1'b1
)(
  input  logic clk_i,
  input  logic rst_ni,

  // The base address of the (heap) memory where to be revocable capabilities point to
  input  logic [31:0] heap_base_addr_i,

  // Upstream port
  input  tlul_pkg::tl_h2d_t upstream_tl_i,
  input  logic              upstream_tag_i,
  output tlul_pkg::tl_d2h_t upstream_tl_o,
  output logic              upstream_tag_o,

  // Downstream port
  output tlul_pkg::tl_h2d_t downstream_tl_o,
  output logic              downstream_tag_o,
  input  tlul_pkg::tl_d2h_t downstream_tl_i,
  input  logic              downstream_tag_i,

  // Revocation bitmap memory port
  output tlul_pkg::tl_h2d_t revbm_tl_o,
  input  tlul_pkg::tl_d2h_t revbm_tl_i,

  // Error signals
  output logic revbm_data_intg_error_o,
  output logic revbm_rsp_intg_error_o,
  output logic revbm_device_error_o
);

  ///////////
  // Types //
  ///////////

  // The padding to 57 bit of the bitmap response fields subject to ECC
  localparam int unsigned RevbmRspIntgPadding = tlul_pkg::D2HRspMaxWidth -
                                                $bits(tlul_pkg::tl_d2h_rsp_intg_t);

  // Size of a full-word access
  localparam int unsigned                WordSizeInt = $clog2(top_pkg::TL_DBW);
  localparam logic [top_pkg::TL_SZW-1:0] WordSize    = top_pkg::TL_SZW'(WordSizeInt);


  /////////////
  // Signals //
  /////////////

  // Signals connecting the upstream-to-downstream (request) fork to the downstream port
  logic us2ds_fork_valid;
  logic us2ds_ready;

  // Signals connecting the downstream-to-upstream (response) join to the upstream port
  logic ds2us_join_ready;
  logic ds2us_valid;

  // Revocation bitmap signals
  logic        revbm_req_valid;
  logic [31:0] revbm_req_addr;
  logic        revbm_rsp_ready;
  logic        revbm_rsp_malformed;
  logic        revbm_rsp_err;

  // Bitmap response ECC signals
  tlul_pkg::tl_d2h_rsp_intg_t revbm_rsp_intg;
  logic [1:0]                 revbm_rsp_intg_error;


  //////////////////////////
  // Protocol-Independent //
  //////////////////////////

  cheriot_trvk_core #(
    .NumOutstanding    (NumOutstanding),
    .RevBitmapAddrWidth(RevBitmapAddrWidth),
    .RevBitmapSizeBytes(RevBitmapSizeBytes),
    .RevBitmapBaseAddr (RevBitmapBaseAddr),
    .MemECC            (MemECC)
  ) u_cheriot_trvk_core (
    .clk_i,
    .rst_ni,
    .heap_base_addr_i,
    .upstream_req_valid_i   (upstream_tl_i.a_valid),
    .upstream_req_ready_o   (us2ds_ready),
    .upstream_req_misalign_i(upstream_tl_i.a_address[2]),
    .upstream_tag_i,
    .upstream_rsp_valid_o   (ds2us_valid),
    .upstream_rsp_ready_i   (upstream_tl_i.d_ready),
    .upstream_tag_o,
    .downstream_req_valid_o (us2ds_fork_valid),
    .downstream_req_ready_i (downstream_tl_i.a_ready),
    .downstream_tag_o,
    .downstream_rsp_valid_i (downstream_tl_i.d_valid),
    .downstream_rsp_ready_o (ds2us_join_ready),
    .downstream_rsp_data_i  (downstream_tl_i.d_data),
    .downstream_tag_i,
    .revbm_req_valid_o      (revbm_req_valid),
    .revbm_req_ready_i      (revbm_tl_i.a_ready),
    .revbm_req_addr_o       (revbm_req_addr),
    .revbm_rsp_valid_i      (revbm_tl_i.d_valid),
    .revbm_rsp_ready_o      (revbm_rsp_ready),
    .revbm_rsp_data_i       (revbm_tl_i.d_data),
    .revbm_rsp_data_intg_i  (revbm_tl_i.d_user.data_intg),
    .revbm_rsp_err_i        (revbm_rsp_err),
    .revbm_data_intg_error_o
  );


  //////////////////////////////////////
  // Upstream to Downstream Intercept //
  //////////////////////////////////////

  // Forward TL payload between upstream and downstream, only intercept handshaking
  always_comb begin : proc_tl_us_ds_connect
    downstream_tl_o         = upstream_tl_i;
    upstream_tl_o           = downstream_tl_i;
    upstream_tl_o.a_ready   = us2ds_ready;
    upstream_tl_o.d_valid   = ds2us_valid;
    downstream_tl_o.a_valid = us2ds_fork_valid;
    downstream_tl_o.d_ready = ds2us_join_ready;
  end


  /////////////////////////
  // Bitmap TL Interface //
  /////////////////////////

  // Assemble read-only request
  always_comb begin : proc_assemble_tl_revbm_req
    // defaults
    revbm_tl_o = tlul_pkg::TL_H2D_DEFAULT;

    revbm_tl_o.a_valid          = revbm_req_valid;
    revbm_tl_o.a_address        = revbm_req_addr;
    revbm_tl_o.a_mask           = '1;
    revbm_tl_o.a_size           = WordSize;
    revbm_tl_o.a_opcode         = tlul_pkg::Get;
    revbm_tl_o.a_user.cmd_intg  = tlul_pkg::get_cmd_intg(revbm_tl_o);
    revbm_tl_o.a_user.data_intg = tlul_pkg::get_data_intg(revbm_tl_o.a_data);
    revbm_tl_o.d_ready          = revbm_rsp_ready;
  end

  // Any error on the bitmap response is treated as revoked, so a corrupted or failed lookup can
  // never let a revoked capability through.
  assign revbm_rsp_err = revbm_tl_i.d_error || revbm_rsp_malformed || (|revbm_rsp_intg_error);

  // A response that is not a full-word AccessAckData is malformed
  assign revbm_rsp_malformed = (revbm_tl_i.d_opcode != tlul_pkg::AccessAckData) ||
                               (revbm_tl_i.d_size != WordSize);

  // Did we receive a device error or a malformed response?
  assign revbm_device_error_o = revbm_tl_i.d_valid && revbm_tl_o.d_ready &&
                                (revbm_tl_i.d_error || revbm_rsp_malformed);

  // Get the response fields subject to ECC
  assign revbm_rsp_intg = tlul_pkg::extract_d2h_rsp_intg(revbm_tl_i);

  // Check the bitmap response integrity
  prim_secded_inv_64_57_dec u_prim_secded_inv_64_57_dec_revbm_rsp (
    .data_i    ({revbm_tl_i.d_user.rsp_intg, {RevbmRspIntgPadding{1'b0}}, revbm_rsp_intg}),
    .data_o    (),
    .syndrome_o(),
    .err_o     (revbm_rsp_intg_error)
  );

  // Mask response integrity error if response is not being handshaked
  assign revbm_rsp_intg_error_o = revbm_tl_i.d_valid && revbm_tl_o.d_ready &&
                                  (|revbm_rsp_intg_error);

  // Bitmap response fields the lookup does not use
  logic unused_revbm_rsp;
  assign unused_revbm_rsp = ^{revbm_tl_i.d_param, revbm_tl_i.d_sink, revbm_tl_i.d_source};

endmodule
