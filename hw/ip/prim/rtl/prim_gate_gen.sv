// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Simple parameterizable gate generator. Used to fill up the netlist
// with gates that cannot be optimized away.
//
// The module leverages 4bit SBoxes from the PRINCE cipher, and interleaves
// them with registers, resulting in a split of around 50/50 between logic and
// sequential cells.
//
// This generator has been tested with 32bit wide data, and it is accurate to
// within around 250 GE. Do not use for fever than 500 GE.
//
// -------------+-----------+----------
// requested GE | actual GE | GE error
// -------------+-----------+----------
// 500          |   679     |   179
// 1000         |   1018    |   18
// 1500         |   1696    |   196
// 2500         |   2714    |   214
// 5000         |   5210    |   210
// 7500         |   7456    |   -44
// 10000        |   10015   |   15
// 15000        |   15191   |   191
// 25000        |   25228   |   228
// 50000        |   50485   |   485
//

module prim_gate_gen #(
  parameter int DataWidth = 32,
  parameter int NumGates = 1000
) (
  input                        clk_i,
  input                        rst_ni,

  input        [DataWidth-1:0] data_i,
  output logic [DataWidth-1:0] data_o
);

  /////////////////////////////////////
  // Local parameters and assertions //
  /////////////////////////////////////

  // technology specific tuning, do not modify.
  // an inner round is comprised of a 2bit rotation, followed by a 4bit SBox Layer.
  localparam int NumInnerRounds = 2;
  localparam int GatesPerRound  = DataWidth * 10;
  // an outer round consists of NumInnerRounds, followed by a register.
  localparam int NumOuterRounds = (NumGates + GatesPerRound / 2) / GatesPerRound;

  // do not use for fewer than 500 GE
  `ASSERT(MinimumNumGates_A, NumGates >= 500)
  `ASSERT(DataMustBeMultipleOfFour_A, DataWidth % 4 == 0)

  /////////////////////
  // Helper Function //
  /////////////////////

  // this is the sbox from the prince cipher
  localparam logic[15:0][3:0] SBox4 = {4'h4, 4'hD, 4'h5, 4'hE,
                                       4'h0, 4'h8, 4'h7, 4'h6,
                                       4'h1, 4'h9, 4'hC, 4'hA,
                                       4'h2, 4'h3, 4'hF, 4'hB};

  function automatic logic [DataWidth-1:0] sbox4_layer(logic [DataWidth-1:0] state_in);
    logic [DataWidth-1:0] state_out;
    // note that if simulation performance becomes an issue, this loop can be unrolled
    for (int k = 0; k < DataWidth/4; k++) begin
      state_out[k*4  +: 4] = SBox4[state_in[k*4  +: 4]];
    end
    return state_out;
  endfunction : sbox4_layer

  /////////////////////
  // Generator Loops //
  /////////////////////

  (* preserve *) logic [NumOuterRounds-1:0][DataWidth-1:0] regs_d, regs_q;

  for (genvar k = 0; k < NumOuterRounds; k++) begin : gen_outer_round

    (* preserve *) logic [NumInnerRounds:0][DataWidth-1:0] inner_data;

    if (k==0) begin : gen_first
      assign inner_data[0] = data_i;
    end else begin : gen_others
      assign inner_data[0] = regs_q[k-1];
    end

    for (genvar l = 0; l < NumInnerRounds; l++) begin : gen_inner
      // 2bit rotation + sbox layer
      assign inner_data[l+1] = sbox4_layer({inner_data[l][1:0], inner_data[l][DataWidth-1:2]});
    end

    assign regs_d[k] = inner_data[NumInnerRounds];
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      regs_q <= '0;
    end else begin
      regs_q <= regs_d;
    end
  end

  assign data_o = regs_q[NumOuterRounds-1];

endmodule : prim_gate_gen
