// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src core module
//

module entropy_src_core #(
  parameter int unsigned EsFifoDepth = 32
) (
  input                  clk_i,
  input                  rst_ni,

  input  entropy_src_reg_pkg::entropy_src_reg2hw_t reg2hw,
  output entropy_src_reg_pkg::entropy_src_hw2reg_t hw2reg,

  output logic           es_entropy_valid_o,
  output logic           es_entropy_fifo_err_o
);

  import entropy_src_reg_pkg::*;

  localparam int unsigned DEPTHW = $clog2(EsFifoDepth+1);

  // signals
  logic [31:0] lfsr_value;
  logic [31:0] seed_value;
  logic        load_seed;
  logic        es_enable;
  logic        es_init;
  logic        esentropy_rd_pls;
  logic        event_es_entropy_valid;
  logic        event_es_entropy_fifo_err;
  logic        sfifo_esentropy_push;
  logic        sfifo_esentropy_pop;
  logic [31:0] sfifo_esentropy_din;
  logic [31:0] sfifo_esentropy_dout;
  logic        sfifo_esentropy_full;
  logic        not_sfifo_esentropy_full;
  logic        sfifo_esentropy_empty;
  logic        not_sfifo_esentropy_empty;
  logic        sfifo_esentropy_err;
  logic [15:0] es_rate;
  logic        es_rate_entropy_valid;
  logic [6:0]  es_reg_fifo_thresh;
  logic [DEPTHW-1:0] es_fifo_thresh;
  logic [DEPTHW-1:0] sfifo_esentropy_depth;

  // flops
  logic        entropy_val_q, entropy_val_d;
  logic [15:0] es_rate_cntr_q, es_rate_cntr_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      entropy_val_q <= '0;
      es_rate_cntr_q <= 16'h0001;
    end else begin
      entropy_val_q <= entropy_val_d;
      es_rate_cntr_q <= es_rate_cntr_d;
    end

  assign es_enable = reg2hw.es_conf.q;
  assign es_init = reg2hw.es_ctrl.q;
  assign load_seed = ((sfifo_esentropy_full & es_init) | ~es_enable);
  assign esentropy_rd_pls = reg2hw.es_entropy.re;

  //--------------------------------------------
  // instantiate interrupt hardware primitives
  //--------------------------------------------

  prim_intr_hw #(.Width(1)) intr_hw_es_entropy_valid (
    .event_intr_i           (event_es_entropy_valid),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.es_entropy_valid.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.es_entropy_valid.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.es_entropy_valid.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.es_entropy_valid.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.es_entropy_valid.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.es_entropy_valid.d),
    .intr_o                 (es_entropy_valid_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_es_entropy_fifo_err (
    .event_intr_i           (event_es_entropy_fifo_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.es_entropy_fifo_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.es_entropy_fifo_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.es_entropy_fifo_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.es_entropy_fifo_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.es_entropy_fifo_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.es_entropy_fifo_err.d),
    .intr_o                 (es_entropy_fifo_err_o)
  );

  //--------------------------------------------
  // lfsr - a version of a entropy source
  //--------------------------------------------

  prim_lfsr #(.LfsrDw(32), .EntropyDw(32), .StateOutDw(32), .DefaultSeed(1), .CustomCoeffs('0))
    u_prim_lfsr (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .seed_en_i      (load_seed),
    .seed_i         (seed_value),
    .lfsr_en_i      (es_enable),
    .entropy_i      ('0),
    .state_o        (lfsr_value)
  );

  // entropy rate limiter

  assign es_rate_cntr_d = ~es_enable ? 16'h0001 :
         (es_rate == '0) ? 16'h0000 :
         es_rate_entropy_valid ? es_rate :
         (es_rate_cntr_q - 1);

  assign es_rate_entropy_valid =
         ~es_enable ? 1'b0 :
         (es_rate == '0) ? 1'b0 :
         (es_rate_cntr_q == 16'h0001);

  //--------------------------------------------
  // fifo for entropy collection
  //--------------------------------------------

  prim_fifo_sync # (.Width(32),.Pass(0),.Depth(EsFifoDepth))
    u_prim_fifo_sync_esentropy (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (~es_enable),
    .wvalid         (sfifo_esentropy_push),
    .wready         (not_sfifo_esentropy_full),
    .wdata          (sfifo_esentropy_din),
    .rvalid         (not_sfifo_esentropy_empty),
    .rready         (sfifo_esentropy_pop),
    .rdata          (sfifo_esentropy_dout),
    .depth          (sfifo_esentropy_depth)
  );

  assign sfifo_esentropy_full = ~not_sfifo_esentropy_full;
  assign sfifo_esentropy_empty = ~not_sfifo_esentropy_empty;
  assign sfifo_esentropy_err =
         (sfifo_esentropy_push & sfifo_esentropy_full) |
         (sfifo_esentropy_empty & sfifo_esentropy_pop);

  // fifo controls
  assign sfifo_esentropy_push = es_enable & es_rate_entropy_valid & ~sfifo_esentropy_full;
  assign sfifo_esentropy_din = lfsr_value;
  assign sfifo_esentropy_pop = es_enable & ~sfifo_esentropy_empty & esentropy_rd_pls;

  // threshold
  assign es_fifo_thresh = es_reg_fifo_thresh[DEPTHW-1:0];

  // entropy valid
  assign entropy_val_d = ~es_enable ? 1'b0 : (sfifo_esentropy_depth >= es_fifo_thresh);

  //--------------------------------------------
  // tlul register settings
  //--------------------------------------------

  // set the es entropy to the read reg
  assign hw2reg.es_entropy.d = sfifo_esentropy_dout;

  // set the es fifo depth to the read reg
  assign hw2reg.es_fdepthst.d = sfifo_esentropy_depth;

  // seed register
  assign seed_value = reg2hw.es_seed.q;

  // es rate register
  assign es_rate = reg2hw.es_rate.q;

  // es fifo threshold register
  assign es_reg_fifo_thresh = reg2hw.es_thresh.q;

  // set the interrupt event when enabled
  assign event_es_entropy_valid = entropy_val_q;

  // set the interrupt sources
  assign event_es_entropy_fifo_err = sfifo_esentropy_err;

  //--------------------------------------------
  // status
  //--------------------------------------------

  // set the status bit
  assign hw2reg.es_status.d = entropy_val_q;

endmodule
