// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////////////////////////
// IMPORTANT NOTE:                                                                                //
//                                   DO NOT USE THIS BLINDLY!                                     //
//                                                                                                //
// This is an initial non-secure prototype of the masking accelerator in OTBN. Details are still  //
// under discussion and subject to change. This code shall not be used in any product.            //
////////////////////////////////////////////////////////////////////////////////////////////////////

module otbn_mask_accelerator
  import otbn_pkg::*; (

  input  logic clk_i,
  input  logic rst_ni,

  // Wipe
  input  logic sec_wipe_running_i,

  // Write port
  input  logic        wvalid_i,
  output logic        wready_o,
  input  logic [31:0] in0_i[2],
  input  logic [31:0] in1_i[2],

  // Randomness
  input  logic [321:0] rand_i,
  input  logic [31:0]  remask_rand_i[2],

  // Config
  input  logic [31:0] mod_i,
  input  mask_op_e    mask_op_i,

  // Read port
  output logic        rvalid_o,
  input  logic        rready_i,
  output logic [31:0] result_o[2],

  // Errors
  output logic mask_fifo_err_o,
  output logic ctr_err_o
);

  localparam int unsigned MaLatency = 18;

  typedef logic [31:0] ma_data_t;

  typedef struct packed {
    logic     valid;
    ma_data_t share_0;
    ma_data_t share_1;
  } ma_pipeline_t;

  // Internal signals
  ma_data_t r_a2b, secret_a2b, sum_a2b, mod_dif_a2b, masked_secret_a2b;
  ma_data_t s_b2a, secret_b2a, dif_b2a, mod_sum_b2a, masked_secret_b2a;
  ma_data_t t, x, y, sum, masked_sum;

  logic c_sum_a2b, c_mod_dif_a2b;
  logic c_dif_b2a;

  ma_pipeline_t [MaLatency-1:0] pipeline_d, pipeline_q;

  // we are always ready to accept data
  assign wready_o = 1'b1;

  // ArithToBool
  // We take a fixed mask `r_a2b`, which satisfies the constraints until the exact design is known.
  assign r_a2b                        = mod_i >> 32'd1;
  assign {c_sum_a2b,     sum_a2b    } = in0_i[0] + in0_i[1];
  assign {c_mod_dif_a2b, mod_dif_a2b} = sum_a2b - mod_i;
  assign secret_a2b                   = c_sum_a2b | c_mod_dif_a2b ? mod_dif_a2b : sum_a2b;
  assign masked_secret_a2b            = secret_a2b ^ r_a2b;

  // BoolToArith
  // We take a fixed mask `s_b2a`, which satisfies the constraints until the exact design is known.
  assign s_b2a                = mod_i >> 32'd1;
  assign secret_b2a           = in0_i[0] ^ in0_i[1];
  assign {c_dif_b2a, dif_b2a} = secret_b2a - s_b2a;
  assign mod_sum_b2a          = dif_b2a + mod_i;
  assign masked_secret_b2a    = c_dif_b2a ? dif_b2a : mod_sum_b2a;

  // SecAdd
  // We take a fixed mask `t`, which satisfies the constraints until the exact design is known.
  assign t          = mod_i >> 32'd1;
  assign x          = in0_i[0] ^ in0_i[1];
  assign y          = in1_i[0] ^ in1_i[1];
  assign sum        = x + y;
  assign masked_sum = sum ^ t;

  always_comb begin : gen_op_sel_mux
    unique case (mask_op_i)
      SecAdd: begin
        pipeline_d[0].valid   = wvalid_i;
        pipeline_d[0].share_0 = wvalid_i ? masked_sum : 32'd0;
        pipeline_d[0].share_1 = wvalid_i ? t          : 32'd0;
      end
      ArithToBool: begin
        pipeline_d[0].valid   = wvalid_i;
        pipeline_d[0].share_0 = wvalid_i ? masked_secret_a2b : 32'd0;
        pipeline_d[0].share_1 = wvalid_i ? r_a2b             : 32'd0;
      end
      BoolToArith: begin
        pipeline_d[0].valid   = wvalid_i;
        pipeline_d[0].share_0 = wvalid_i ? masked_secret_b2a : 32'd0;
        pipeline_d[0].share_1 = wvalid_i ? s_b2a             : 32'd0;
      end
      default: begin
        pipeline_d[0].valid   = 1'b0;
        pipeline_d[0].share_0 = 32'd0;
        pipeline_d[0].share_1 = 32'd0;
      end
    endcase
  end

  // The results are computed instantaneous, the results are then passed through N pipeline
  // registers to emulate the latency of computation.
  for (genvar i = 1; i < MaLatency; i++) begin : gen_shift_pipeline
    assign pipeline_d[i] = pipeline_q[i-1];
  end

  // state
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_ma_pipeline_state
    if (!rst_ni) begin
      pipeline_q <= '0;
    end else begin
      pipeline_q <= pipeline_d;
    end
  end

  // assign outputs
  assign result_o[0] = pipeline_q[MaLatency-1].share_0;
  assign result_o[1] = pipeline_q[MaLatency-1].share_1;
  assign rvalid_o = pipeline_q[MaLatency-1].valid;

  // Unused inputs are tied-off
  logic unused_ma;
  assign unused_ma = ^{rready_i, sec_wipe_running_i, rand_i, remask_rand_i[0], remask_rand_i[1]};

  // No errors internally
  assign mask_fifo_err_o = 1'b0;
  assign ctr_err_o       = 1'b0;

endmodule
