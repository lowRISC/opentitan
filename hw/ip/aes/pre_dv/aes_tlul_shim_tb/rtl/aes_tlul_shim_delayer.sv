// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module aes_tlul_shim_delayer
  import tlul_pkg::*;
#(
  parameter bit DelayerEnable = 1
) (
  input logic clk_i,
  input logic rst_ni,

  input tl_h2d_t tl_h2d_i,
  input tl_d2h_t tl_d2h_i,

  output tl_h2d_t tl_h2d_delayed_o,
  output tl_d2h_t tl_d2h_delayed_o
);

  logic tlul_pass;

  generate
    if (DelayerEnable) begin : gen_delay_logic
      logic [3:0] delay_cntr_d, delay_cntr_q;

      logic lfsr_en;
      logic [3:0] lfsr_out;

      // 8-bit LFSR with a period of 2^8-1 and 4-bit output.
      prim_lfsr #(
        .LfsrDw     ( 8 ),
        .StateOutDw ( 4 )
      ) u_prim_lfsr (
        .clk_i     ( clk_i    ),
        .rst_ni    ( rst_ni   ),
        .seed_en_i ( '0       ),
        .seed_i    ( '0       ),
        .lfsr_en_i ( lfsr_en  ),
        .entropy_i ( '0       ),
        .state_o   ( lfsr_out )
      );

      // The delay counter is active when `tl_d2h_i.d_valid`. Until the max value is reached
      // `tl_h2d_i.d_ready` and `tl_d2h_i.d_valid` are pulled down. The counter remains at the max
      // value until the device-to-host response is acknowledged. This is robust even in the case
      // when the `tl_d2h_i.d_valid` is deasserted without having received a host-side
      // acknowledgement.
      assign tlul_pass = delay_cntr_q == lfsr_out;
      assign lfsr_en = tlul_pass & tl_h2d_i.d_ready & tl_d2h_i.d_valid;

      always_comb begin
        delay_cntr_d = delay_cntr_q;
        if (lfsr_en) begin
          delay_cntr_d = 0;
        end else if (tl_d2h_i.d_valid) begin
          delay_cntr_d = delay_cntr_q + 1'b1;
        end
      end

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          delay_cntr_q <= 0;
        end else begin
          delay_cntr_q <= delay_cntr_d;
        end
      end
    end else begin : gen_no_delay
      assign tlul_pass = 1'b1;

      logic unused_signals;
      assign unused_signals = ^{clk_i, rst_ni};
    end
  endgenerate


  // A delay is created by manually pulling down `d_valid` and `d_ready`
  // which offsets the TLUL response.
  assign tl_h2d_delayed_o = '{
    a_valid: tl_h2d_i.a_valid,
    a_opcode: tl_h2d_i.a_opcode,
    a_size: tl_h2d_i.a_size,
    a_mask: tl_h2d_i.a_mask,
    a_source: tl_h2d_i.a_source,
    a_address: tl_h2d_i.a_address,
    a_data: tl_h2d_i.a_data,
    a_user: tl_h2d_i.a_user,
    d_ready: tl_h2d_i.d_ready & tlul_pass,
    a_param: tl_h2d_i.a_param
  };

  assign tl_d2h_delayed_o = '{
    d_valid: tl_d2h_i.d_valid & tlul_pass,
    d_opcode: tl_d2h_i.d_opcode,
    d_param: tl_d2h_i.d_param,
    d_size: tl_d2h_i.d_size,
    d_source: tl_d2h_i.d_source,
    d_sink: tl_d2h_i.d_sink,
    d_data: tl_d2h_i.d_data,
    d_user: tl_d2h_i.d_user,
    d_error: tl_d2h_i.d_error,
    a_ready: tl_d2h_i.a_ready
  };

endmodule
