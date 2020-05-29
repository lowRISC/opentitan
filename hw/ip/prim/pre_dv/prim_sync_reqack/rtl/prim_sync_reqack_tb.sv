// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Scratch verification testbench for REQ/ACK synchronizer primitive

module prim_sync_reqack_tb #(
) (
  input  logic clk_i,
  input  logic rst_ni,

  output logic test_done_o,
  output logic test_passed_o
);

  // TB configuration
  localparam int unsigned NumTransactions = 8;
  localparam logic        FastToSlow = 1'b1; // Select 1'b0 for SlowToFast
  localparam int unsigned Ratio = 4; // must be even and greater equal 2

  // Derivation of parameters
  localparam int unsigned Ticks = Ratio/2;
  localparam int unsigned WidthTicks = $clog2(Ticks)+1;
  localparam int unsigned WidthTrans = $clog2(NumTransactions)+1;

  // Derive slow clock (using a counter)
  logic [WidthTicks-1:0] count_clk_d, count_clk_q;
  assign count_clk_d = count_clk_q == (Ticks[WidthTicks-1:0]-1) ? '0 : count_clk_q + {{WidthTicks-1{1'b0}},{1'b1}};
  always_ff @(posedge clk_i) begin : reg_count_clk
    count_clk_q <= count_clk_d;
  end

  logic clk_slow_d, clk_slow_q, clk_slow;
  assign clk_slow_d = count_clk_q == (Ticks[WidthTicks-1:0]-1) ? !clk_slow_q : clk_slow_q;
  always_ff @(posedge clk_i) begin : reg_clk_slow
    clk_slow_q <= clk_slow_d;
  end
  assign clk_slow = clk_slow_q;

  // Sync reset to slow clock
  logic [1:0] rst_slow_nq;
  logic       rst_slow_n;
  always_ff @(posedge clk_slow) begin
    rst_slow_nq <= {rst_slow_nq[0], rst_ni};
  end
  assign rst_slow_n = rst_ni & rst_slow_nq[1];

  // Connect clocks
  logic clk_src, clk_dst;
  assign clk_src = FastToSlow ? clk_i    : clk_slow;
  assign clk_dst = FastToSlow ? clk_slow : clk_i;

  logic src_req, dst_req;
  logic src_ack, dst_ack;
  logic rst_done;

  // Instantiate DUT
  prim_sync_reqack prim_sync_reqack (
    .clk_src_i  (clk_src),
    .rst_src_ni (rst_slow_n),
    .clk_dst_i  (clk_dst),
    .rst_dst_ni (rst_slow_n),

    .src_req_i  (src_req),
    .src_ack_o  (src_ack),
    .dst_req_o  (dst_req),
    .dst_ack_i  (dst_ack)
  );

  // Make sure we do not apply stimuli before the reset.
  always_ff @(posedge clk_slow or negedge rst_slow_n) begin
    if (!rst_slow_n) begin
      rst_done <= '1;
    end else begin
      rst_done <= rst_done;
    end
  end

  // Create randomized ACK delay
  localparam int WIDTH_COUNT = 3;
  logic [31:0]             tmp;
  logic [31-WIDTH_COUNT:0] unused_tmp;
  assign unused_tmp = tmp[31:WIDTH_COUNT];
  logic [WIDTH_COUNT-1:0]  dst_count_clk_d, dst_count_clk_q;
  logic [WIDTH_COUNT-1:0]  dst_count_clk_max_d, dst_count_clk_max_q;
  logic                    count_exp;
  assign count_exp = dst_count_clk_q == dst_count_clk_max_q;
  always_comb begin
    dst_count_clk_d     = dst_count_clk_q;
    dst_count_clk_max_d = dst_count_clk_max_q;
    tmp                 = '0;
    if (dst_req && count_exp) begin
      // Clear counter
      dst_count_clk_d = '0;
      // Get new max
      tmp = $random;
      dst_count_clk_max_d = tmp[2:0];
    end else if (dst_req) begin
      // Increment
      dst_count_clk_d = dst_count_clk_q + {{WIDTH_COUNT-1{1'b0}},{1'b1}};
    end
  end
  always_ff @(posedge clk_dst or negedge rst_slow_n) begin : reg_dst_count_clk
    if (!rst_slow_n) begin
      dst_count_clk_q     <= '0;
      dst_count_clk_max_q <= '0;
    end else begin
      dst_count_clk_q     <= dst_count_clk_d;
      dst_count_clk_max_q <= dst_count_clk_max_d;
    end
  end

  // Apply stimuli
  always_comb begin

    src_req = 1'b0;
    dst_ack = 1'b0;

    if (rst_done && rst_slow_n) begin
      // The source wants to perform handshakes at maximum rate.
      src_req = 1'b1;
    end

    if (dst_req && count_exp) begin
      // The destination sends the ACK after a random delay.
      dst_ack = 1'b1;
    end
  end

  // Count handshakes on both sides
  logic [WidthTrans-1:0] src_count_d, src_count_q;
  logic [WidthTrans-1:0] dst_count_d, dst_count_q;
  assign src_count_d = (src_req && src_ack) ? src_count_q + 1'b1 : src_count_q;
  always_ff @(posedge clk_src or negedge rst_slow_n) begin : reg_src_count
    if (!rst_slow_n) begin
      src_count_q <= '0;
    end else begin
      src_count_q <= src_count_d;
    end
  end
  assign dst_count_d = (dst_req && dst_ack) ? dst_count_q + 1'b1 : dst_count_q;
  always_ff @(posedge clk_dst or negedge rst_slow_n) begin : reg_dst_count
    if (!rst_slow_n) begin
      dst_count_q <= '0;
    end else begin
      dst_count_q <= dst_count_d;
    end
  end

  // Check responses, signal end of simulation
  always_ff @(posedge clk_i) begin : tb_ctrl
    test_done_o   <= 1'b0;
    test_passed_o <= 1'b1;

    if ((src_count_q == NumTransactions[WidthTrans-1:0]) &&
        (dst_count_q == NumTransactions[WidthTrans-1:0])) begin // Success

      $display("\nSUCCESS: Performed %0d handshakes in both source and destination domain.",
          NumTransactions);
      $display("Finishing simulation now.\n");
      test_passed_o <= 1'b1;
      test_done_o   <= 1'b1;
    end else if (((src_count_q > dst_count_q) && ((src_count_q - dst_count_q) > 1)) ||
                 ((dst_count_q > src_count_q) && ((dst_count_q - src_count_q) > 1))) begin // Failed
      $display("\nERROR: Performed %0d handshakes in source domain, and %0d in destination domain.",
          src_count_q, dst_count_q);
      $display("Finishing simulation now.\n");
      test_passed_o <= 1'b0;
      test_done_o   <= 1'b1;
    end
  end

endmodule
