// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_racl_error_arb
  import top_racl_pkg::*;
#(
  parameter int unsigned N = 8
) (
  input  logic            clk_i,
  input  logic            rst_ni,
  input  racl_error_log_t error_log_i[N],
  output racl_error_log_t error_log_o
);
  // Extract error valid to be used for the arbiter as a request signal
  logic [N-1:0] error_valid, any_valid_overflow;
  for (genvar i = 0; i < N; i++) begin : gen_extract_valid
    assign error_valid[i]        = error_log_i[i].valid;
    assign any_valid_overflow[i] = error_log_i[i].valid & error_log_i[i].overflow;
  end

  // If there are multiple errors in the same cycle, arbitrate and get the first error.
  // Lower index in error_valid has higher priority.
  logic [$bits(racl_error_log_t)-1:0] racl_error_logic;
  racl_error_log_t                    racl_error_arb;
  logic [N-1:0]                       gnt;

  prim_arbiter_fixed #(
    .N  ( N                       ),
    .DW ( $bits(racl_error_log_t) )
  ) u_prim_err_arb (
    .clk_i,
    .rst_ni,
    .req_i    ( error_valid      ),
    .data_i   ( error_log_i      ),
    .gnt_o    ( gnt              ),
    .idx_o    (                  ),
    .valid_o  (                  ),
    .data_o   ( racl_error_logic ),
    .ready_i  ( 1'b1             )
  );
  assign racl_error_arb = racl_error_log_t'(racl_error_logic);

  // Assert the overflow if:
  //   1. a valid incoming error already asserted the overflow
  //   2. there are multiple errors occurring simultaneously, but only one is granted by the
  //      arbiter. See if another request is there besides out the masked granted one.
  logic overflow;
  assign overflow = |any_valid_overflow | (racl_error_arb.valid & |(error_valid & ~gnt));

  // Assemble dinal arbitrated RACL error based on the arbitrated error and the computed overflow.
  assign error_log_o.valid           = racl_error_arb.valid;
  assign error_log_o.racl_role       = racl_error_arb.racl_role;
  assign error_log_o.ctn_uid         = racl_error_arb.ctn_uid;
  assign error_log_o.read_access     = racl_error_arb.read_access;
  assign error_log_o.request_address = racl_error_arb.request_address;
  assign error_log_o.overflow        = overflow;

  // Arbitrated overflow is not used
  logic unused_signals;
  assign unused_signals = racl_error_arb.overflow;
endmodule
