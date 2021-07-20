// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Asynchronous implementation of prim_subreg_ext

module prim_subreg_ext_async #(
  parameter int unsigned DW = 32
) (
  input          clk_src_i,
  input          rst_src_ni,
  input          clk_dst_i,
  input          rst_dst_ni,

  // source domain signals
  input          re,
  input          we,
  input [DW-1:0] wd,
  input          src_update_i,
  output logic   src_busy_o,

  // destination domain signals
  input [DW-1:0] d,

  // outputs to destination domain
  output logic          qe,
  output logic          qre,
  output logic [DW-1:0] q,

  // outputs to source domain
  output logic [DW-1:0] qs
);

  logic dst_req;
  logic [DW-1:0] dst_wdata;
  logic dst_we;
  logic unused_src_we;

  // Capture both data and write-enable
  // write enable is needed to determine whether qe or qre should be generated
  // in the desitnation domain.
  prim_subreg_cdc #(
    .DW(DW + 1)
  ) u_reg_cdc (
    .clk_src_i,
    .rst_src_ni,
    .clk_dst_i,
    .rst_dst_ni,
    .src_update_i,
    .src_req_i(re | we),
    .src_data_i({wd, we}),
    .src_data_o({qs, unused_src_we}),
    .src_busy_o,
    .dst_req_o(dst_req),
    .dst_data_i({d, 1'b0}),
    .dst_data_o({dst_wdata, dst_we})
  );

  /////////////////////
  // Destination domain
  /////////////////////

  assign qe  = dst_req ? dst_we    : '0;
  assign qre = dst_req ? ~dst_we   : '0;
  assign q   = dst_req ? dst_wdata : '0;


endmodule
