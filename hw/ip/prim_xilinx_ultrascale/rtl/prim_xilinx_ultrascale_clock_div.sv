// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_xilinx_ultrascale_clock_div #(
  parameter int unsigned Divisor = 2,
  parameter logic ResetValue = 0
) (
  input clk_i,
  input rst_ni,
  input step_down_req_i, // step down divisor by 2x
  output logic step_down_ack_o, // step down acknowledge
  input test_en_i,
  output logic clk_o
);


  // Only even divide is supported at the moment
  // For odd divide we need to introduce more parameters to control duty cycle
  `ASSERT_INIT(DivEven_A, (Divisor % 2) == 0)

  // It is assumed the flops in this module are NOT on the scan-chain, as a result only
  // the input values are guarded
  logic step_down_req;
  assign step_down_req = test_en_i ? '0 : step_down_req_i;

  if (Divisor <= 8) begin : gen_div_bufg
    logic clk_div_full, clk_div_stepdown;

    BUFGCE_DIV #(
      .BUFGCE_DIVIDE(Divisor),
      .IS_CLR_INVERTED(1'b1)
    ) u_bufg_div_full (
      .CE(1'b1),
      .CLR(rst_ni),
      .I(clk_i),
      .O(clk_div_full)
    );

    BUFGCE_DIV #(
      .BUFGCE_DIVIDE(Divisor / 2),
      .IS_CLR_INVERTED(1'b1)
    ) u_bufg_div_stepdown (
      .CE(1'b1),
      .CLR(rst_ni),
      .I(clk_i),
      .O(clk_div_stepdown)
    );

    logic clk_div_stepdown_en, clk_div_full_en;
    always_ff @(negedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        clk_div_full_en     <= 1'b0;
        clk_div_stepdown_en <= 1'b0;
      end else begin
        clk_div_full_en     <= !step_down_req;
        clk_div_stepdown_en <= step_down_req;
      end
    end

    BUFGCTRL #(
      .INIT_OUT(ResetValue)
    ) u_bufg_div_mux (
      .CE0(1'b1),
      .CE1(1'b1),
      .S0(clk_div_full_en),
      .S1(clk_div_stepdown_en),
      .I0(clk_div_full),
      .I1(clk_div_stepdown),
      .O(clk_o)
    );

  assign step_down_ack_o = clk_div_stepdown_en;

  end else begin : gen_div_no_bufg

    localparam int unsigned ToggleCnt = Divisor / 2;
    localparam int unsigned CntWidth = $clog2(ToggleCnt);
    logic clk_int;
    logic [CntWidth-1:0] cnt;
    logic [CntWidth-1:0] limit;

    assign limit = !step_down_req       ? CntWidth'(ToggleCnt - 1) :
                   (ToggleCnt / 2) == 2 ? '0 : CntWidth'((ToggleCnt / 2) - 1);

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        cnt <= '0;
        clk_int <= ResetValue;
      end else if (cnt >= limit) begin
        cnt <= '0;
        clk_int <= ~clk_o;
      end else begin
        cnt <= cnt + 1'b1;
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        step_down_ack_o <= 1'b0;
      end else begin
        step_down_ack_o <= step_down_req;
      end
    end

    // anchor points for constraints
    logic clk_muxed;
    prim_clock_mux2 #(
      .NoFpgaBufG(1'b1)
    ) u_clk_mux (
      .clk0_i(clk_int),
      .clk1_i(clk_i),
      .sel_i('0),
      .clk_o(clk_muxed)
    );

    prim_clock_buf u_clk_div_buf (
      .clk_i(clk_muxed),
      .clk_o
    );
  end

endmodule
