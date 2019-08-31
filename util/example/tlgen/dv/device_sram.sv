// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module device_sram (
  input clk_i,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o
);

  import tlul_pkg::*;

  logic [31:0] storage [*];

  initial begin
    tl_o.a_ready = 1'b1;
    tl_o.d_valid = 1'b0;

    forever begin
      @(posedge clk_i iff (tl_i.a_valid == 1'b1));
      tl_o.d_error = 1'b0;
      tl_o.d_source = tl_i.a_source;
      tl_o.d_size = tl_i.a_size;
      tl_o.d_sink = 0;
      tl_o.d_param = 2'h0;
      tl_o.d_user = 'h0;
      if (tl_i.a_opcode == Get) begin
        if (storage.exists(tl_i.a_address[31:2])) begin
          tl_o.d_data = storage[tl_i.a_address[31:2]];
        end else begin
          tl_o.d_data = $urandom();
          storage[tl_i.a_address[31:2]] = tl_o.d_data;
        end

        tl_o.a_ready = 1'b0;
        tl_o.d_opcode = AccessAckData;
        tl_o.d_valid = 1'b1;
        @(posedge clk_i iff (tl_i.d_ready == 1'b1));
        tl_o.d_valid = 1'b0;
        tl_o.a_ready = 1'b1;
      end else if (tl_i.a_opcode == PutFullData) begin
        storage[tl_i.a_address[31:2]] = tl_i.a_data;
        tl_o.a_ready = 1'b0;
        tl_o.d_opcode = AccessAck;
        tl_o.d_valid = 1'b1;
        @(posedge clk_i iff (tl_i.d_ready == 1'b1));
        tl_o.d_valid = 1'b0;
        tl_o.a_ready = 1'b1;
      end
    end
  end

endmodule
