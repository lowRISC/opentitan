// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Basic testbench for prim_flop_2sync with CDC random delay enabled.
module tb;
  `include "dv_macros.svh"

  localparam string MsgId = $sformatf("%m");

  logic [31:0] src_d, src_q;
  wire clk, rst_n;

  clk_rst_if clk_rst_if(.clk, .rst_n);

  prim_flop_2sync #(.Width(32)) dut (
    // source clock domain
    .d_i    (src_d),
    // destination clock domain
    .clk_i  (clk),
    .rst_ni (rst_n),
    .q_o    (src_q)
  );

  initial begin
    clk_rst_if.set_active();
    clk_rst_if.apply_reset(.reset_width_clks(10));

    $display("Using prim_cdc_rand_delay_mode slow");
    dut.u_prim_cdc_rand_delay.set_prim_cdc_rand_delay_mode(1);
    repeat (100) begin
      src_d <= $urandom();
      clk_rst_if.wait_clks($urandom_range(1, 20));
    end
    clk_rst_if.wait_clks(200);

    $display("Using prim_cdc_rand_delay_mode once");
    dut.u_prim_cdc_rand_delay.set_prim_cdc_rand_delay_mode(2);
    repeat (100) begin
      src_d <= $urandom();
      clk_rst_if.wait_clks($urandom_range(1, 20));
    end
    clk_rst_if.wait_clks(200);

    $display("Using prim_cdc_rand_delay_mode interval = 10");
    dut.u_prim_cdc_rand_delay.set_prim_cdc_rand_delay_mode(3);
    dut.u_prim_cdc_rand_delay.set_prim_cdc_rand_delay_interval(10);
    repeat (100) begin
      src_d <= $urandom();
      clk_rst_if.wait_clks($urandom_range(1, 20));
    end
    clk_rst_if.wait_clks(200);

    $display("Using prim_cdc_rand_delay_mode interval = 1");
    dut.u_prim_cdc_rand_delay.set_prim_cdc_rand_delay_interval(1);
    repeat (100) begin
      src_d <= $urandom();
      clk_rst_if.wait_clks($urandom_range(1, 20));
    end
    clk_rst_if.wait_clks(200);

    $display("Using prim_cdc_rand_delay_mode interval = 0");
    dut.u_prim_cdc_rand_delay.set_prim_cdc_rand_delay_interval(0);
    repeat (100) begin
      src_d <= $urandom();
      clk_rst_if.wait_clks($urandom_range(1, 20));
    end
    clk_rst_if.wait_clks(200);

    // TODO: Add more checks.
    dv_test_status_pkg::dv_test_status(.passed(1));
    `DV_CHECK(!src_d_q.size(), , , MsgId)
    $finish;
  end

  // Verify src_d to src_q consistency.
  logic [31:0] src_d_q[$];
  initial begin
    fork
      forever @src_d if (rst_n) src_d_q.push_back(src_d);
      forever @src_q `DV_CHECK_EQ(src_q, src_d_q.pop_front(), , , MsgId)
    join_none
  end

endmodule
