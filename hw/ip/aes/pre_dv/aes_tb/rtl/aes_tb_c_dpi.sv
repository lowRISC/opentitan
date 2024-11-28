// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This module serves as the interface to the `c_dpi` API by instantiating the function call as a
// combinatorial block. The `c_dpi` output (data and tag) is flopped and the 32 least significant
// bits of data and tag become visible at the module's output ports in the next clock cycle. The
// flopped data and tag can be rotated by 32 positions to the right to make other bits visible.

module aes_tb_c_dpi
  import aes_pkg::*;
  import aes_model_dpi_pkg::*;
  import aes_tb_pkg::*;
#(
    parameter int ADLength = 0,
    parameter int DataLength = 16
) (
   input logic clk_i,
   input logic rst_ni,

   input c_dpi_input_t c_dpi_input_i,

   input logic c_dpi_load_i,         // Flop `c_dpi` output.
   input logic c_dpi_rotate_data_i,  // Rotate data >> 32.
   input logic c_dpi_rotate_tag_i,   // Rotate tag  >> 32.

   output logic [31:0] c_dpi_data_o,
   output logic [31:0] c_dpi_tag_o
);

  // Make the 32 least signification bits of data and tag visible at the output ports.

  assign c_dpi_data_o = {c_dpi_data_q[3], c_dpi_data_q[2], c_dpi_data_q[1], c_dpi_data_q[0]};
  assign c_dpi_tag_o  = c_dpi_tag_q[31:0];

  // Flop the output data acquired from the `c_dpi` API in an unpacked array of at least 4 bytes.

  logic [7:0] c_dpi_data   [max(4, DataLength)];
  logic [7:0] c_dpi_data_d [max(4, DataLength)];
  logic [7:0] c_dpi_data_q [max(4, DataLength)];

  always_comb begin
    c_dpi_data_d = c_dpi_data_q;
    if (c_dpi_load_i) begin
      c_dpi_data_d = c_dpi_data;
    end else if (c_dpi_rotate_data_i) begin
      for (int i = 0; i < DataLength; i++) begin
        c_dpi_data_d[i] = c_dpi_data_q[(i + 4) % DataLength];
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      c_dpi_data_q <= '{default: '0};
    end else begin
      c_dpi_data_q <= c_dpi_data_d;
    end
  end

  // Flop the output tag acquired from the `c_dpi` API in the encryption case. The `c_dpi` API does
  // not output the tag in the decryption case, consequently it needs to be input by the testbench
  // itself. Note that the byte ordering of the `c_dpi` and HW tag differ.

  logic [127:0] c_dpi_tag;
  logic [127:0] c_dpi_tag_d;
  logic [127:0] c_dpi_tag_q;

  always_comb begin
    c_dpi_tag_d = c_dpi_tag_q;
    if (c_dpi_load_i) begin
      if (c_dpi_input_i.operation == AES_ENC) begin
        c_dpi_tag_d = aes_transpose(c_dpi_tag);
      end else begin
        c_dpi_tag_d = c_dpi_input_i.tag;
      end
    end else if (c_dpi_rotate_tag_i) begin
      c_dpi_tag_d = {c_dpi_tag_q[31:0], c_dpi_tag_q[127:32]};
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      c_dpi_tag_q <= '0;
    end else begin
      c_dpi_tag_q <= c_dpi_tag_d;
    end
  end

  // As of version 4.210, the only way of transforming a packed array into an unpacked one (required
  // by the `c_dpi`) in a Verilator simulation is by manually reassigning the signals.

  logic [7:0] c_dpi_ad_unp   [max(1, ADLength)];
  logic [7:0] c_dpi_data_unp [max(1, DataLength)];

  always_comb begin
    for (int i = 0; i < ADLength; i++) begin
      c_dpi_ad_unp[i] = c_dpi_input_i.ad[i];
    end
    for (int i = 0; i < DataLength; i++) begin
      c_dpi_data_unp[i] = c_dpi_input_i.data[i];
    end
  end

  always_comb begin
    if (ADLength == 0 && DataLength == 0) begin
      c_dpi_aes_crypt_message(
        1'b1,
        c_dpi_input_i.operation[1],
        c_dpi_input_i.mode,
        c_dpi_input_i.iv,
        c_dpi_input_i.key_length,
        c_dpi_input_i.key,
        '0,
        '0,
        c_dpi_input_i.tag,
        c_dpi_data,
        c_dpi_tag
      );
    end else if (ADLength == 0 && DataLength > 0) begin
      c_dpi_aes_crypt_message(
        1'b1,
        c_dpi_input_i.operation[1],
        c_dpi_input_i.mode,
        c_dpi_input_i.iv,
        c_dpi_input_i.key_length,
        c_dpi_input_i.key,
        c_dpi_data_unp,
        '0,
        c_dpi_input_i.tag,
        c_dpi_data,
        c_dpi_tag
      );
    end else if (ADLength > 0 && DataLength == 0) begin
      c_dpi_aes_crypt_message(
        1'b1,
        c_dpi_input_i.operation[1],
        c_dpi_input_i.mode,
        c_dpi_input_i.iv,
        c_dpi_input_i.key_length,
        c_dpi_input_i.key,
        '0,
        c_dpi_ad_unp,
        c_dpi_input_i.tag,
        c_dpi_data,
        c_dpi_tag
      );
    end else begin
      c_dpi_aes_crypt_message(
        1'b1,
        c_dpi_input_i.operation[1],
        c_dpi_input_i.mode,
        c_dpi_input_i.iv,
        c_dpi_input_i.key_length,
        c_dpi_input_i.key,
        c_dpi_data_unp,
        c_dpi_ad_unp,
        c_dpi_input_i.tag,
        c_dpi_data,
        c_dpi_tag
      );
    end
  end

endmodule
