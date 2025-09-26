// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The purpose of this module is to have a small and simple module that can be synthesized (and its
// netlist can be inspected) for easy constraint checking.
// The synthesis tool is not allowed to perform constant propagation, merging of redundant signals,
// and performing logic optimization accross preserved cells.
//
// 1. In the synthesized netlist, the following number of size_only instances must be present:
// e.g. grep -c -R u_size_only_x netlist.v (make sure the design is uniquified)
// |-------------------------------------------------------------------|
// | Test | buf | and2 | xor | xnor | flop | clock_mux2 | clock_gating |
// | -----| ----|------|-----|------|------|------------|--------------|
// | 1    | 192 | -    |  -  | -    | -    | -          | -            |
// | 2    | -   | -    |  64 | -    | -    | -          | -            |
// | 3    |  48 | 48   |  48 | 48   | 144  | -          | -            |
// | 4    |   8 |  8   |   8 |  8   |  24  | -          | -            |
// | 5    |  36 | -    |  -  | -    |  24  | -          | -            |
// | 6    |  16 | -    |  -  | -    |   8  | -          | -            |
// | 7    | -   | -    |  -  | -    |  32  | 2          | 2            |
// | 8    |  16 | -    |  -  | -    |   8  | -          | -            |
// | 9    |  12 | -    |  -  | -    |  12  | -          | -            |
// | -----| ----|------|-----|------|------|------------|--------------|
// |total | 328 | 56   | 120 | 56   | 252  | 2          | 2            |
// |-------------------------------------------------------------------|
//
// 2. None of the test_*_o signals can be driven by a constant 0 or 1.
// The instantiated size_only instances must prevent logic optimizations and keep
// the output comparators
// e.g. check_design -constant
//
// 3. None of the buffers or flip flops can be unloaded:
// e.g. check_design -unloaded_comb -unloaded
//
// 4. lc_en_o, mubi_o signals cannot be driven to a constant value
// (optimization accross preserevd instances cannot happen)
//
// 5. lc_en_i, mubi_i signals can only be connected to variables, or legal mubi/lc values
// e.g. grep -oE '(\.lc_en_i|\.mubi_i) \([^)]+'  netlist.v

`include "prim_assert.sv"

module prim_sdc_example #(
  localparam int unsigned Width = 8, // these localparams are constant, don't override
  localparam int unsigned NumSender = 4,
  localparam int unsigned NumTests = 12,
  localparam int unsigned NumSenderLc = 2,
  localparam int unsigned NumTestsLc = 6
) (
  input logic                                    clk_i,
  input logic                                    rst_ni,

  input  logic [31:0]                            data_a_i,
  input  logic [31:0]                            data_b_i,
  input  logic [31:0]                            data_c_i,

  input  logic                                   en_i,

  output logic [31:0]                            test_res_o,
  output logic                                   test_xor_o,
  output logic                                   test_const_o,
  output logic                                   test_var_o,
  output logic [1:0]                             test_mubi_out_o,
  output logic [NumSender-1:0][NumTests-1:0]     test_mubi_bool_out_o,
  output logic [3:0][Width-1:0]                  test_clk_gen_o,
  output logic [1:0]                             test_lc_out_o,
  output logic [NumSenderLc-1:0][NumTestsLc-1:0] test_lc_bool_out_o
);

  import prim_mubi_pkg::*;

  //////////////////////////////////////////////////////
  // Test 1: basic buffers with arithmetic operations //
  //////////////////////////////////////////////////////
  // It is not allowed that arithmetic operations are merged across prim_bufs
  // The following size_only cells are expected:
  // 6*32 size_only_buf

  localparam int unsigned NumStages = 3;
  localparam int unsigned ConstA = 32'h0FF0_ABBA;

  logic [NumStages-1:0][31:0] res, res_buf;
  logic [31:0] data_a, data_b, data_c;

  prim_buf #(
    .Width(32)
  ) u_prim_buf_data_a (
    .in_i (data_a_i),
    .out_o(data_a)
  );

  prim_buf #(
    .Width(32)
  ) u_prim_buf_data_b (
    .in_i (data_b_i),
    .out_o(data_b)
  );

  prim_buf #(
    .Width(32)
  ) u_prim_buf_data_c (
    .in_i (data_c_i),
    .out_o(data_c)
  );

  assign res[0] = data_a + data_b;

  prim_buf #(
    .Width(32)
  ) u_prim_buf_res0 (
    .in_i (res[0]),
    .out_o(res_buf[0])
  );

  assign res[1] = res_buf[0] + ConstA;

  prim_buf #(
    .Width(32)
  ) u_prim_buf_res1 (
    .in_i (res[1]),
    .out_o(res_buf[1])
  );

  assign res[2] = res_buf[1] * data_c;

  prim_buf #(
    .Width(32)
  ) u_prim_buf_res2 (
    .in_i (res[2]),
    .out_o(res_buf[2])
  );

  assign test_res_o = res_buf[2];

  ////////////////////////////////////////////////////////////////
  // Test 2: two xor operations in a row result in the identity //
  ////////////////////////////////////////////////////////////////
  // This optimization is prevented by the preserved instances
  // The following size_only cells are expected:
  // 2*32 size_only_xor2
  // test_xor_o must be the result of a comparison and not tied to high

  logic [31:0] res_xor2_0, res_xor2_1;

  prim_xor2 #(
    .Width(32)
  ) u_prim_xor2_0 (
    .in0_i(data_a_i),
    .in1_i(data_b_i),
    .out_o(res_xor2_0)
  );

  prim_xor2 #(
    .Width(32)
  ) u_prim_xor2_1 (
    .in0_i(res_xor2_0),
    .in1_i(data_b_i),
    .out_o(res_xor2_1)
  );

  // The comparison below is always true because
  // res_xor2_1 = res_xor2_0 ^ data_b_i = data_a_i ^ data_b_i ^ data_b_i = data_a_i
  // But the comparison cannot be optimized because logic propagation is not allowed
  // across preserved instances
  assign test_xor_o = (res_xor2_1 == data_a_i) ? 1'b1 : 1'b0;

  //////////////////////////////////////////////////////////
  // Test 3: prim basic gates tests with constant inputs: //
  //////////////////////////////////////////////////////////
  // These gates cannot be removed
  // The following size_only cells are expected:
  // 6*8 size_only_buf
  // 6*8 size_only_and2
  // 6*8 size_only_xor
  // 6*8 size_only_xnor
  // 6*8*3 size_only_flop

  localparam int unsigned NumConst = 6;
  localparam int unsigned NumGates = 7;

  localparam logic [Width-1:0] ConstIn0 [NumConst] = {8'hAB,
                                                      8'hBA,
                                                      8'h01,
                                                      8'hFE,
                                                      8'hF0,
                                                      8'h0F};

  localparam logic [Width-1:0] ConstIn1 [NumConst] = {8'h10,
                                                      8'h25,
                                                      8'h39,
                                                      8'hBC,
                                                      8'hD1,
                                                      8'h5F};

  logic [NumConst-1:0][NumGates-1:0][Width-1:0] const_out_not_removed;

  for (genvar idx = 0; idx < NumConst; idx++) begin : g_num_consts
    prim_buf #(
      .Width(Width)
    ) u_prim_buf (
      .in_i (ConstIn0[idx]),
      .out_o(const_out_not_removed[idx][0])
    );

    prim_and2 #(
      .Width(Width)
    ) u_prim_and2 (
      .in0_i(ConstIn0[idx]),
      .in1_i(ConstIn1[idx]),
      .out_o(const_out_not_removed[idx][1])
    );

    prim_xor2 #(
      .Width(Width)
    ) u_prim_xor2 (
      .in0_i(ConstIn0[idx]),
      .in1_i(ConstIn1[idx]),
      .out_o(const_out_not_removed[idx][2])
    );

    prim_xnor2 #(
      .Width(Width)
    ) u_prim_xnor2 (
      .in0_i(ConstIn0[idx]),
      .in1_i(ConstIn1[idx]),
      .out_o(const_out_not_removed[idx][3])
    );

    prim_flop #(
     .Width(Width)
    ) u_prim_flop (
      .clk_i (clk_i),
      .rst_ni(rst_ni),
      .d_i   (ConstIn0[idx]),
      .q_o   (const_out_not_removed[idx][4])
    );

    prim_flop_en #(
     .Width(Width)
    ) u_prim_flop_en (
      .clk_i (clk_i),
      .rst_ni(rst_ni),
      .en_i  (en_i),
      .d_i   (ConstIn0[idx]),
      .q_o   (const_out_not_removed[idx][5])
    );

    prim_flop_no_rst #(
     .Width(Width)
    ) u_prim_flop_no_rst (
      .clk_i(clk_i),
      .d_i  (ConstIn0[idx]),
      .q_o  (const_out_not_removed[idx][6])
    );
  end

  assign test_const_o = ^const_out_not_removed;

  ///////////////////////////////////////////////////
  // Test 4: prim basic gates with variable inputs //
  ///////////////////////////////////////////////////
  // The following size_only cells are expected:
  // 8 size_only_buf
  // 8 size_only_and2
  // 8 size_only_xor
  // 8 size_only_xnor
  // 8*3 size_only_flop

  logic [NumGates-1:0][Width-1:0] var_out_not_removed;

  prim_buf #(
      .Width(Width)
  ) u_prim_buf (
      .in_i (data_a[Width-1:0]),
      .out_o(var_out_not_removed[0])
  );
  prim_and2 #(
      .Width(Width)
  ) u_prim_and2 (
      .in0_i(data_a[Width-1:0]),
      .in1_i(data_b[Width-1:0]),
      .out_o(var_out_not_removed[1])
  );
  prim_xor2 #(
      .Width(Width)
  ) u_prim_xor2 (
      .in0_i(data_a[Width-1:0]),
      .in1_i(data_b[Width-1:0]),
      .out_o(var_out_not_removed[2])
  );
  prim_xnor2 #(
      .Width(Width)
  ) u_prim_xnor2 (
      .in0_i(data_a[Width-1:0]),
      .in1_i(data_b[Width-1:0]),
      .out_o(var_out_not_removed[3])
  );
  prim_flop #(
      .Width(Width)
  ) u_prim_flop (
      .clk_i (clk_i),
      .rst_ni(rst_ni),
      .d_i   (data_a[Width-1:0]),
      .q_o   (var_out_not_removed[4])
  );
  prim_flop_en #(
      .Width(Width)
  ) u_prim_flop_en (
      .clk_i (clk_i),
      .rst_ni(rst_ni),
      .en_i  (en_i),
      .d_i   (data_a[Width-1:0]),
      .q_o   (var_out_not_removed[5])
  );
  prim_flop_no_rst #(
      .Width(Width)
  ) u_prim_flop_no_rst (
      .clk_i(clk_i),
      .d_i  (data_a[Width-1:0]),
      .q_o  (var_out_not_removed[6])
  );

  assign test_var_o = ^var_out_not_removed;

  ///////////////////////////////////////////////
  // Test 5: mubi4_sender with constant inputs //
  ///////////////////////////////////////////////
  // Constant mubi signals cannot be used to perform optimizations at the output
  // The following size_only cells are expected:
  // 9*4 size_only_buf
  // 4*6 size_only_flop

  mubi4_t [NumSender-1:0] mubi4_true_out;
  mubi4_t [NumSender-1:0] mubi4_false_out;
  mubi4_t [NumSender-1:0] mubi4_var_out;

  prim_mubi4_sender #(
    .AsyncOn(0),
    .EnSecBuf(0)
  ) u_mubi4_sender_true0 (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .mubi_i(MuBi4True),
    .mubi_o(mubi4_true_out[0])
  );

  prim_mubi4_sender #(
    .AsyncOn(0),
    .EnSecBuf(0)
  ) u_mubi4_sender_false0 (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .mubi_i(MuBi4False),
    .mubi_o(mubi4_false_out[0])
  );

  prim_mubi4_sender #(
    .AsyncOn(0),
    .EnSecBuf(0)
  ) u_mubi4_sender_var0 (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .mubi_i(mubi4_bool_to_mubi(data_a_i[0])),
    .mubi_o(mubi4_var_out[0])
  );

  prim_mubi4_sender #(
    .AsyncOn(1),
    .EnSecBuf(0)
  ) u_mubi4_sender_true1 (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .mubi_i(MuBi4True),
    .mubi_o(mubi4_true_out[1])
  );

  prim_mubi4_sender #(
    .AsyncOn(1),
    .EnSecBuf(0)
  ) u_mubi4_sender_false1 (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .mubi_i(MuBi4False),
    .mubi_o(mubi4_false_out[1])
  );

  prim_mubi4_sender #(
    .AsyncOn(1),
    .EnSecBuf(0)
  ) u_mubi4_sender_var1 (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .mubi_i(mubi4_bool_to_mubi(data_a_i[1])),
    .mubi_o(mubi4_var_out[1])
  );

  prim_mubi4_sender #(
    .AsyncOn(0),
    .EnSecBuf(1)
  ) u_mubi4_sender_true2 (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .mubi_i(MuBi4False),
    .mubi_o(mubi4_true_out[2])
  );

  prim_mubi4_sender #(
    .AsyncOn(0),
    .EnSecBuf(1)
  ) u_mubi4_sender_false2 (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .mubi_i(MuBi4False),
    .mubi_o(mubi4_false_out[2])
  );

  prim_mubi4_sender #(
    .AsyncOn(0),
    .EnSecBuf(1)
  ) u_mubi4_sender_var2 (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .mubi_i(mubi4_bool_to_mubi(data_a_i[2])),
    .mubi_o(mubi4_var_out[2])
  );

  prim_mubi4_sender #(
    .AsyncOn(1),
    .EnSecBuf(1)
  ) u_mubi4_sender_true3 (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .mubi_i(MuBi4False),
    .mubi_o(mubi4_true_out[3])
  );

  prim_mubi4_sender #(
    .AsyncOn(1),
    .EnSecBuf(1)
  ) u_mubi4_sender_false3 (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .mubi_i(MuBi4False),
    .mubi_o(mubi4_false_out[3])
  );

  prim_mubi4_sender #(
    .AsyncOn(1),
    .EnSecBuf(1)
  ) u_mubi4_sender_var3 (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .mubi_i(mubi4_bool_to_mubi(data_a_i[3])),
    .mubi_o(mubi4_var_out[3])
  );

  // none of these bool_out can be tied directly to low/high
  for (genvar idx = 0; idx < NumSender; idx++) begin : g_out
    assign test_mubi_bool_out_o[idx][0]  = mubi4_test_true_strict(mubi4_true_out[idx]);
    assign test_mubi_bool_out_o[idx][1]  = mubi4_test_true_loose(mubi4_true_out[idx]);
    assign test_mubi_bool_out_o[idx][2]  = mubi4_test_false_strict(mubi4_true_out[idx]);
    assign test_mubi_bool_out_o[idx][3]  = mubi4_test_false_loose(mubi4_true_out[idx]);
    assign test_mubi_bool_out_o[idx][4]  = mubi4_test_true_strict(mubi4_false_out[idx]);
    assign test_mubi_bool_out_o[idx][5]  = mubi4_test_true_loose(mubi4_false_out[idx]);
    assign test_mubi_bool_out_o[idx][6]  = mubi4_test_false_strict(mubi4_false_out[idx]);
    assign test_mubi_bool_out_o[idx][7]  = mubi4_test_false_loose(mubi4_false_out[idx]);
    assign test_mubi_bool_out_o[idx][8]  = mubi4_test_true_strict(mubi4_var_out[idx]);
    assign test_mubi_bool_out_o[idx][9]  = mubi4_test_true_loose(mubi4_var_out[idx]);
    assign test_mubi_bool_out_o[idx][10] = mubi4_test_false_strict(mubi4_var_out[idx]);
    assign test_mubi_bool_out_o[idx][11] = mubi4_test_false_loose(mubi4_var_out[idx]);
  end

  //////////////////////////////
  // Test 6: mubi_sync_copies //
  //////////////////////////////
  // These gates cannot be removed
  // The following size_only cells are expected:
  // 2*2*4 size_only_buf
  // 4*2 size_only_flop

  localparam int unsigned NumCopies = 2;

  mubi4_t [NumCopies-1:0] mubi_var0, mubi_var1;
  mubi4_t [1:0] mubi_var_comp;

  prim_mubi4_sync #(
    .NumCopies(NumCopies),
    .AsyncOn(0)
  ) u_prim_mubi4_sync0 (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .mubi_i(mubi4_bool_to_mubi(data_a_i[0])),
    .mubi_o(mubi_var0)
  );

  prim_mubi4_sync #(
    .NumCopies(NumCopies),
    .AsyncOn(1)
  ) u_prim_mubi4_sync1 (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .mubi_i(mubi4_bool_to_mubi(data_b_i[0])),
    .mubi_o(mubi_var1)
  );

  // These comparisons can be simplified to just mubi_var0/1 but the sythesizer is not allowed to
  // perform the optimizations
  assign mubi_var_comp[0] = mubi4_or_hi (mubi_var0[0], mubi_var0[1]);
  assign mubi_var_comp[1] = mubi4_and_hi(mubi_var1[0], mubi_var1[1]);

  assign test_mubi_out_o[0] = mubi4_test_false_loose(mubi_var_comp[0]);
  assign test_mubi_out_o[1] = mubi4_test_true_loose(mubi_var_comp[1]);

  ///////////////////////////////
  // Test 7: test_clock_gating //
  ///////////////////////////////
  // clock gate cannot be removed
  // The following size_only cells are expected:
  // 2 size_only_clock_gating
  // 2 size_only_clock_mux2
  // 2*2*8 size_only_flop

  logic [1:0]             clk, clk_muxed;

  // cannot be removed even though clock is always on/off
  prim_clock_gating u_prim_clk_gate_const0 (
    .clk_i    (clk_i),
    .en_i     (1'b0),
    .test_en_i(1'b0),
    .clk_o    (clk[0])
  );
  prim_clock_gating u_prim_clk_gate_const1 (
    .clk_i    (clk_i),
    .en_i     (1'b1),
    .test_en_i(1'b0),
    .clk_o    (clk[1])
  );

  // mux cannot be removed even though select is constant
  prim_clock_mux2 u_prim_clock_mux_const0 (
    .clk0_i(clk_i),
    .clk1_i(1'b0),
    .sel_i (1'b0),
    .clk_o (clk_muxed[0])
  );

  // mux cannot be removed even though select and clkinput is constant
  prim_clock_mux2 u_prim_clock_mux_const1 (
    .clk0_i(clk_i),
    .clk1_i(1'b0),
    .sel_i (1'b1),
    .clk_o (clk_muxed[1])
  );

  for (genvar idx = 0; idx < 2; idx++) begin : g_flops
    prim_flop #(
      .Width(Width)
    ) u_prim_flop_clk_const (
      .clk_i (clk[idx]),
      .rst_ni(rst_ni),
      .d_i   (data_a[Width-1:0]),
      .q_o   (test_clk_gen_o[0+2*idx])
    );
    prim_flop #(
      .Width(Width)
    ) u_prim_flop_clk_muxed (
      .clk_i (clk_muxed[idx]),
      .rst_ni(rst_ni),
      .d_i   (data_b[Width-1:0]),
      .q_o   (test_clk_gen_o[1+2*idx])
    );
  end

  //////////////////////////
  // Test 8: lc_sync test //
  //////////////////////////
  // All copies must be present and output logic cannot be optimized
  // The following size_only cells are expected:
  // 2*2*4 size_only_buf
  // 4*2 size_only_flop

  localparam int unsigned NumCopiesLc = 2;
  import lc_ctrl_pkg::*;

  lc_tx_t [NumCopiesLc-1:0] lc_var0, lc_var1;
  lc_tx_t [1:0]             lc_var_comp;

  prim_lc_sync #(
    .NumCopies(NumCopiesLc),
    .AsyncOn(0)
  ) u_prim_lc_sync0 (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .lc_en_i(lc_tx_bool_to_lc_tx(data_a_i[0])),
    .lc_en_o(lc_var0)
  );

  prim_lc_sync #(
    .NumCopies(NumCopiesLc),
    .AsyncOn(1)
  ) u_prim_lc_sync1 (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .lc_en_i(lc_tx_bool_to_lc_tx(data_b_i[0])),
    .lc_en_o(lc_var1)
  );

  // These comparisons can be simplified to just lc_var0/1 but the sythesizer is not allowed to
  // perform the optimizations
  assign lc_var_comp[0] = lc_tx_or_hi (lc_var0[0], lc_var0[1]);
  assign lc_var_comp[1] = lc_tx_and_hi(lc_var1[0], lc_var1[1]);

  assign test_lc_out_o[0] = lc_tx_test_false_loose(lc_var_comp[0]);
  assign test_lc_out_o[1] = lc_tx_test_true_loose(lc_var_comp[1]);

  ////////////////////////////
  // Test 9: lc_sender test //
  ////////////////////////////
  // Send different lc_en signals through prim_sender and perform constant comparisons
  // Output comparisons cannot be removed and output xor tree must remain
  // The following size_only cells are expected:
  // 3*4 size_only_buf
  // 3*4 size_only_flop

  lc_tx_t [NumSenderLc-1:0] lc_on_out;
  lc_tx_t [NumSenderLc-1:0] lc_off_out;
  lc_tx_t [NumSenderLc-1:0] lc_var_out;

  prim_lc_sender #(
    .AsyncOn(0)
  ) u_lc_sender_on0 (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .lc_en_i(On),
    .lc_en_o(lc_on_out[0])
  );

  prim_lc_sender #(
    .AsyncOn(0)
  ) u_lc_sender_off0 (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .lc_en_i(Off),
    .lc_en_o(lc_off_out[0])
  );

  prim_lc_sender #(
    .AsyncOn(0)
  ) u_lc_sender_var0 (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .lc_en_i(lc_tx_bool_to_lc_tx(data_a_i[0])),
    .lc_en_o(lc_var_out[0])
  );

  prim_lc_sender #(
    .AsyncOn(1)
  ) u_lc_sender_on1 (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .lc_en_i(On),
    .lc_en_o(lc_on_out[1])
  );

  prim_lc_sender #(
    .AsyncOn(1)
  ) u_lc_sender_off1 (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .lc_en_i(Off),
    .lc_en_o(lc_off_out[1])
  );

  prim_lc_sender #(
    .AsyncOn(1)
  ) u_lc_sender_var1 (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .lc_en_i(lc_tx_bool_to_lc_tx(data_a_i[1])),
    .lc_en_o(lc_var_out[1])
  );

  // none of these lc_bool_out can be tied directly to low/high
  for (genvar idx = 0; idx < NumSenderLc; idx++) begin : g_lc_bool_out
    assign test_lc_bool_out_o[idx][0] = lc_tx_test_true_strict(lc_on_out[idx]);
    assign test_lc_bool_out_o[idx][1] = lc_tx_test_false_strict(lc_on_out[idx]);
    assign test_lc_bool_out_o[idx][2] = lc_tx_test_true_loose(lc_off_out[idx]);
    assign test_lc_bool_out_o[idx][3] = lc_tx_test_false_loose(lc_off_out[idx]);
    assign test_lc_bool_out_o[idx][4] = lc_tx_test_invalid(lc_var_out[idx]);
    assign test_lc_bool_out_o[idx][5] = lc_tx_test_true_strict(lc_var_out[idx]);
 end

endmodule : prim_sdc_example
