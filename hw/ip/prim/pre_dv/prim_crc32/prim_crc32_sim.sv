// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_crc32_sim (
  input IO_CLK,
  input IO_RST_N
);
  logic [47:0] test_crc_in;
  logic [31:0] test_data;
  logic [31:0] crc_out;
  logic [31:0] cnt;
  logic        set_crc;

  assign test_crc_in = {cnt[7:0], cnt[7:0], test_data};

  always @(posedge IO_CLK or negedge IO_RST_N) begin
    if (!IO_RST_N) begin
      test_data <= 32'hdeadbeee;
      cnt <= '0;
      set_crc <= 1'b0;
    end else begin
      if (cnt == 0) begin
        set_crc <= 1'b1;
        cnt <= cnt + 32'd1;
      end else if (cnt < 100) begin
        set_crc <= 1'b0;
        test_data <= test_data + 32'd1;
        cnt <= cnt + 32'd1;

        $display("%08x", crc_out);
      end else begin
        $finish();
      end
    end
  end

  prim_crc32 #(.BytesPerWord(6)) dut (
    .clk_i(IO_CLK),
    .rst_ni(IO_RST_N),

    .set_crc_i(set_crc),
    .crc_in_i(32'h00000000),

    .data_valid_i(~set_crc),
    .data_i(test_crc_in),
    .crc_out_o(crc_out)
  );

endmodule
