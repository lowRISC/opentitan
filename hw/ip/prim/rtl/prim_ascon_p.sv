// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Ascon round function implementation


module prim_ascon_p (
output logic [319:0] state_o,
input  logic [319:0] state_i,
input  logic   [3:0] round_i,
input  logic   [3:0] version_i
);

logic [319:0] ark_w, sbox_w;


// Add round constant
logic [7:0] rcon [12];

logic [3:0] addr_w;

assign rcon[ 0] = 'hf0;
assign rcon[ 1] = 'he1;
assign rcon[ 2] = 'hd2;
assign rcon[ 3] = 'hc3;
assign rcon[ 4] = 'hb4;
assign rcon[ 5] = 'ha5;
assign rcon[ 6] = 'h96;
assign rcon[ 7] = 'h87;
assign rcon[ 8] = 'h78;
assign rcon[ 9] = 'h69;
assign rcon[10] = 'h58;
assign rcon[11] = 'h4b;

// The versions of Ascon permutation
assign addr_w = round_i + (12-version_i);

assign ark_w = state_i ^ {64'h0, 64'h0, 56'h0, rcon[addr_w], 64'h0, 64'h0};

// Substitution layer

logic [63:0] x_w  [5];
logic [ 4:0] xtranspose_w [64];
logic [ 4:0] ytranspose_w [64];
logic [63:0] y_w  [5];

genvar i;

assign x_w[0] = ark_w[ 63:  0];
assign x_w[1] = ark_w[127: 64];
assign x_w[2] = ark_w[191:128];
assign x_w[3] = ark_w[255:192];
assign x_w[4] = ark_w[319:256];

generate
  for (i = 0; i < 64; i = i + 1) begin : gen_sbox_transpose
    assign xtranspose_w[i] = {x_w[4][i], x_w[3][i], x_w[2][i], x_w[1][i], x_w[0][i]};
    prim_ascon_sbox sbox (.state_i(xtranspose_w[i]), .state_o(ytranspose_w[i]));
    assign {y_w[4][i], y_w[3][i], y_w[2][i], y_w[1][i], y_w[0][i]} = ytranspose_w[i];
  end
endgenerate

assign sbox_w = {y_w[4], y_w[3], y_w[2], y_w[1], y_w[0]};

// linear layer

logic [63:0] xl_w [5];
logic [63:0] yl_w [5];

assign xl_w[0] = sbox_w[ 63:  0];
assign xl_w[1] = sbox_w[127: 64];
assign xl_w[2] = sbox_w[191:128];
assign xl_w[3] = sbox_w[255:192];
assign xl_w[4] = sbox_w[319:256];

assign yl_w[0] = xl_w[0] ^ {xl_w[0][18:0], xl_w[0][63:19]} ^ {xl_w[0][27:0], xl_w[0][63:28]};
assign yl_w[1] = xl_w[1] ^ {xl_w[1][60:0], xl_w[1][63:61]} ^ {xl_w[1][38:0], xl_w[1][63:39]};
assign yl_w[2] = xl_w[2] ^ {xl_w[2][   0], xl_w[2][63: 1]} ^ {xl_w[2][ 5:0], xl_w[2][63: 6]};
assign yl_w[3] = xl_w[3] ^ {xl_w[3][ 9:0], xl_w[3][63:10]} ^ {xl_w[3][16:0], xl_w[3][63:17]};
assign yl_w[4] = xl_w[4] ^ {xl_w[4][ 6:0], xl_w[4][63: 7]} ^ {xl_w[4][40:0], xl_w[4][63:41]};

assign state_o = {yl_w[4], yl_w[3], yl_w[2], yl_w[1], yl_w[0]};


endmodule
