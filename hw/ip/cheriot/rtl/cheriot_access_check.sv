// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module cheriot_access_check #(
  // TL-UL address type
  parameter type   addr_t                = logic [top_pkg::TL_AW-1:0],
  // Start address (inclusive)
  parameter addr_t CheriotBaseAddr       = 'h0,
  // End address (non-inclusive)
  parameter addr_t CheriotTopAddr        = 'h1,
  // Are we allowed to `PutPartialData` in CHERIoT mode?
  parameter bit    CheriotSubWordAllowed = 1'b0
) (
  input  logic clk_i,
  input  logic rst_ni,

  // CHERIoT mode enabled
  input  prim_mubi_pkg::mubi4_t cheriot_ena_i,

  // TL host port
  input  tlul_pkg::tl_h2d_t tl_h_i,
  output tlul_pkg::tl_d2h_t tl_h_o,

  // TL device port
  output tlul_pkg::tl_h2d_t tl_d_o,
  input  tlul_pkg::tl_d2h_t tl_d_i
);

  import tlul_pkg::*;


  /////////////
  // Signals //
  /////////////

  tlul_pkg::tl_h2d_t tl_demux_h2d[32'd2];
  tlul_pkg::tl_d2h_t tl_demux_d2h[32'd2];

  tlul_pkg::tl_h2d_t tl_err_h2d;
  tlul_pkg::tl_d2h_t tl_err_d2h;

  logic allow_forward;
  logic allowed_operation;


  ////////////////////
  // Access Checker //
  ////////////////////

  always_comb begin: proc_allow_forward

    // Default: do not forward
    allow_forward     = 1'b0;
    allowed_operation = 1'b0;

    // CHERIoT mode enabled
    if(prim_mubi_pkg::mubi4_test_true_strict(cheriot_ena_i)) begin

      // Check whether we have a valid operation
      allowed_operation = CheriotSubWordAllowed                                     ?
                          tl_h_i.a_opcode inside {PutFullData, PutPartialData, Get} :
                          tl_h_i.a_opcode inside {PutFullData, Get};

      // Forward if address range is valid, operation is allowed, and we can use the device in
      // the currently active mode.
      allow_forward = tl_h_i.a_address >= CheriotBaseAddr &&
                      tl_h_i.a_address <  CheriotTopAddr  &&
                      allowed_operation;

    // CHERIoT mode disabled: no access
    end else if (prim_mubi_pkg::mubi4_test_false_strict(cheriot_ena_i)) begin
      allow_forward = 1'b0;

    // Something else; redirect to error response
    end else begin
      allow_forward = 1'b0;
    end
  end


  ///////////////
  // TL Muxing //
  ///////////////

  tlul_socket_1n #(
    .N(32'd2),
    .HReqDepth('h0),
    .HRspDepth('h0),
    .DReqDepth('h0),
    .DRspDepth('h0),
    .ExplicitErrs(1'b0)
  ) u_tlul_socket_1n (
    .clk_i,
    .rst_ni,
    .tl_h_i      ( tl_h_i ),
    .tl_h_o      ( tl_h_o ),
    .tl_d_o      ( tl_demux_h2d   ),
    .tl_d_i      ( tl_demux_d2h   ),
    .dev_select_i( !allow_forward )
  );

  assign tl_d_o     = tl_demux_h2d[0];
  assign tl_err_h2d = tl_demux_h2d[1];

  assign tl_demux_d2h[0] = tl_d_i;
  assign tl_demux_d2h[1] = tl_err_d2h;

  tlul_err_resp #(
    .ReturnBlankResp(1'b0)
  ) u_tlul_err_resp (
    .clk_i,
    .rst_ni,
    .tl_h_i(tl_err_h2d),
    .tl_h_o(tl_err_d2h)
  );

endmodule
