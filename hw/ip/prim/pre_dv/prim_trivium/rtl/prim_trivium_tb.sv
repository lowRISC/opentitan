// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Scratch verification testbench for Trivium/Bivium stream cipher primitives

module prim_trivium_tb (
  input  logic clk_i,
  input  logic rst_ni,

  output logic test_done_o,
  output logic test_passed_o
);

  import prim_trivium_pkg::*;

  // TB configuration
  localparam int unsigned OutputWidth = 128;
  localparam int unsigned PartialSeedWidth = 32;

  localparam int unsigned TriviumLastStatePartFractional =
      TriviumStateWidth % PartialSeedWidth != 0 ? 1 : 0;
  localparam int unsigned TriviumNumStateParts =
      TriviumStateWidth / PartialSeedWidth + TriviumLastStatePartFractional;
  localparam int unsigned BiviumLastStatePartFractional =
      BiviumStateWidth % PartialSeedWidth != 0 ? 1 : 0;
  localparam int unsigned BiviumNumStateParts =
      BiviumStateWidth / PartialSeedWidth + BiviumLastStatePartFractional;

  // Counter to control the simulation.
  localparam int unsigned CountWidth = 10;
  logic [CountWidth-1:0] count_d, count_q;
  assign count_d = count_q + 10'd1;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_count
    if (!rst_ni) begin
      count_q <= '0;
    end else begin
      count_q <= count_d;
    end
  end

  /////////////
  // Trivium //
  /////////////
  // Test vectors seem to be available for Trivium only. Thus only the Trivium instances are really
  // verified against a known good key stream.

  // In case the OutputWidth is not a divisor of 1152, the key stream is offset by the remainder of
  // this division. Thus, we skip the checking of the instance seeded with key and IV.
  localparam bit SkipSeedKeyIvInstance = 1152 % OutputWidth != '0;
  localparam int unsigned TestVectorOutLen = 512;
  localparam int unsigned NumOutputsToCheck = TestVectorOutLen / OutputWidth;
  localparam int unsigned NumOutputBitsToCheck = NumOutputsToCheck * OutputWidth;
  localparam int unsigned OutCtrWidth = prim_util_pkg::vbits(NumOutputsToCheck) + 1;
  localparam int NumInstances = 3;

  logic trivium_en, trivium_seed_en;
  logic trivium_seed_ack_seed_state_partial;
  logic trivium_seed_done_seed_key_iv;
  logic trivium_seed_done_seed_state_full;
  logic trivium_seed_done_seed_state_partial;
  logic [KeyIvWidth-1:0] seed_key, seed_iv;
  logic [TriviumStateWidth-1:0] seed_state_full;
  logic [PartialSeedWidth-1:0] trivium_seed_state_partial;
  logic [OutputWidth-1:0] key_seed_key_iv, key_seed_state_full, key_seed_state_partial;

  // Trivium test vectors generated using
  //
  // https://asecuritysite.com/encryption/trivium
  //
  // Notes on the test vectors from the above site:
  // - key and IV are 'byte' vectors starting with Byte n (most left) and ending with Byte 0 (most
  //   right). Within each byte, the LSB is the most left bit and the MSB being the
  //   most right bit.
  // - The key stream is a 'byte' vector starting with Byte 0 (most left) and ending with
  //   Byte n (most right). Within each byte, the LSB is the most right bit and the MSB being the
  //   most left bit.
  //
  // In this testbench, we use bit vectors only with LSB being most left and the MSB being most
  // right.
  logic [TestVectorOutLen-1:0] key_stream_expected;

  // // key = 0
  // // iv = 0
  // localparam logic [KeyIvWidth-1:0] VECTOR_0_KEY = 80'h0000_0000_0000_0000_0000;
  // localparam logic [KeyIvWidth-1:0] VECTOR_0_IV = 80'h0000_0000_0000_0000_0000;
  // localparam logic [TestVectorOutLen-1:0] VECTOR_0_KEY_STREAM =
  //     {128'hF2D4_A5B5_4C1A_8003_5980_746E_9849_5528,
  //      128'h9A59_A29A_751A_4C2B_38B7_6802_0392_52F7,
  //      128'hCDE9_B2A1_0F79_A8E7_2DCF_0719_1603_3256,
  //      128'h7FC9_9F23_4E2E_7A51_1B05_5958_26BF_E0FB};
  // localparam logic [TriviumStateWidth-1:0] VECTOR_0_STATE =
  //     {96'h92AC_487E_267F_5871_D3A1_896D,
  //      96'hF514_AD2F_EA84_1320_40AE_4058,
  //      96'hA21B_38EC_692A_E61D_7493_1A85};

  // // key = 8000_0000_0000_0000_0000
  // // iv = 0
  // localparam logic [KeyIvWidth-1:0] VECTOR_1_KEY = 80'h0100_0000_0000_0000_0000;
  // localparam logic [KeyIvWidth-1:0] VECTOR_1_IV = 80'h0000_0000_0000_0000_0000;
  // localparam logic [TestVectorOutLen-1:0] VECTOR_1_KEY_STREAM =
  //     {128'hF980_FC54_74EF_E87B_B962_6ACC_CC20_FF98,
  //      128'h807F_CFCE_928F_6CE0_EB21_0961_15F5_FBD2,
  //      128'h649A_F249_C241_2055_0175_C864_1465_7BBB,
  //      128'h0D54_2044_3AF1_8DAF_9C7A_0D73_FF86_EB38};
  // localparam logic [TriviumStateWidth-1:0] VECTOR_1_STATE =
  //     {96'hC7D7_C89B_CC06_725B_3D94_7181,
  //      96'h06F2_A065_6422_AF1F_A457_B81F,
  //      96'h0D25_16A9_D565_893A_64C1_E50E};

  // key = 0A5D_B003_56A9_FC4F_A2F5
  // iv =  1F86_ED54_BB22_89F0_57BE
  localparam logic [KeyIvWidth-1:0] VECTOR_2_KEY = 80'h50BA_0DC0_6A95_3FF2_45AF;
  localparam logic [KeyIvWidth-1:0] VECTOR_2_IV = 80'hF861_B72A_DD44_910F_EA7D;
  localparam logic [TestVectorOutLen-1:0] VECTOR_2_KEY_STREAM =
      {128'h7258_8CB7_89E3_8615_0DFC_DA03_BDA3_A5AE,
       128'h2F98_426C_4C75_C0F1_3BFB_6B2D_E2DD_6E54,
       128'hB8F0_AB03_51B7_F538_3C17_FAC1_E8B0_913B,
       128'h1838_E884_56D9_D2D0_ADCB_4B13_C510_94DE};
  localparam logic [TriviumStateWidth-1:0] VECTOR_2_STATE =
      {96'hE843_DB60_EB48_14D1_C198_620D,
       96'hF21B_0322_0BAD_DAD5_A15A_3958,
       96'hBC97_5171_D8C0_4C75_B395_11C4};

  assign seed_key = VECTOR_2_KEY;
  assign seed_iv = VECTOR_2_IV;
  assign seed_state_full = VECTOR_2_STATE;
  assign key_stream_expected = VECTOR_2_KEY_STREAM;

  // Instantiate DUTs
  prim_trivium #(
    .BiviumVariant(0),
    .OutputWidth  (OutputWidth),
    .SeedType     (SeedTypeKeyIv)
  ) u_prim_trivium_seed_key_iv (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .en_i                (trivium_en),
    .allow_lockup_i      (1'b0),
    .seed_en_i           (trivium_seed_en),
    .seed_done_o         (trivium_seed_done_seed_key_iv),
    .seed_req_o          (),
    .seed_ack_i          (trivium_seed_en),
    .seed_key_i          (seed_key),
    .seed_iv_i           (seed_iv),
    .seed_state_full_i   ('0), // unused
    .seed_state_partial_i('0), // unused

    .key_o(key_seed_key_iv),
    .err_o()
  );

  prim_trivium #(
    .BiviumVariant(0),
    .OutputWidth  (OutputWidth),
    .SeedType     (SeedTypeStateFull)
  ) u_prim_trivium_seed_state_full (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .en_i                (trivium_en),
    .allow_lockup_i      (1'b0),
    .seed_en_i           (trivium_seed_en),
    .seed_done_o         (trivium_seed_done_seed_state_full),
    .seed_req_o          (),
    .seed_ack_i          (trivium_seed_en),
    .seed_key_i          ('0), // unused
    .seed_iv_i           ('0), // unused
    .seed_state_full_i   (seed_state_full),
    .seed_state_partial_i('0), // unused

    .key_o(key_seed_state_full),
    .err_o()
  );

  prim_trivium #(
    .BiviumVariant   (0),
    .OutputWidth     (OutputWidth),
    .SeedType        (SeedTypeStatePartial),
    .PartialSeedWidth(PartialSeedWidth)
  ) u_prim_trivium_seed_state_partial (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .en_i                (trivium_en),
    .allow_lockup_i      (1'b0),
    .seed_en_i           (trivium_seed_en),
    .seed_done_o         (trivium_seed_done_seed_state_partial),
    .seed_req_o          (),
    .seed_ack_i          (trivium_seed_ack_seed_state_partial),
    .seed_key_i          ('0), // unused
    .seed_iv_i           ('0), // unused
    .seed_state_full_i   ('0), // unused
    .seed_state_partial_i(trivium_seed_state_partial),

    .key_o(key_seed_state_partial),
    .err_o()
  );

  // Tracking of seed_done
  logic [NumInstances-1:0] trivium_seed_done_d, trivium_seed_done_q;
  assign trivium_seed_done_d = (trivium_seed_done_q &
      // Clear back to zero upon staring a new reseed operation.
      {NumInstances{~trivium_seed_en}}) |
      // Register finishing of reseed operation.
      {trivium_seed_done_seed_state_partial,
       trivium_seed_done_seed_state_full,
       trivium_seed_done_seed_key_iv};
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_trivium_seed_done
    if (!rst_ni) begin
      trivium_seed_done_q <= '0;
    end else begin
      trivium_seed_done_q <= trivium_seed_done_d;
    end
  end

  // Start the reseed operation right after coming out of reset.
  assign trivium_seed_en = count_q == 10'd1;
  // Start running once all instances have finished the reseed operation.
  assign trivium_en = &trivium_seed_done_q;

  // Provide the 9 partial seed parts.
  assign trivium_seed_ack_seed_state_partial =
      (count_q >= 10'd1) && (count_q < 10'd1 + TriviumNumStateParts[CountWidth-1:0]);
  assign trivium_seed_state_partial =
      seed_state_full[({22'h0, count_q} - 32'd1) * PartialSeedWidth +: PartialSeedWidth];

  /////////////////////////////////
  // Record generated key streams//
  /////////////////////////////////
  logic record;
  assign record = trivium_en & (out_ctr_q < NumOutputsToCheck[OutCtrWidth-1:0]);

  logic [OutCtrWidth-1:0] out_ctr_d, out_ctr_q;
  assign out_ctr_d = record ? out_ctr_q + 1'b1 : out_ctr_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_out_ctr
    if (!rst_ni) begin
      out_ctr_q <= '0;
    end else begin
      out_ctr_q <= out_ctr_d;
    end
  end

  logic [TestVectorOutLen-1:0] key_stream_actual_d [NumInstances];
  logic [TestVectorOutLen-1:0] key_stream_actual_q [NumInstances];
  always_comb begin
    key_stream_actual_d = key_stream_actual_q;
    if (record) begin
      key_stream_actual_d[0][out_ctr_q * OutputWidth +: OutputWidth] = key_seed_key_iv;
      key_stream_actual_d[1][out_ctr_q * OutputWidth +: OutputWidth] = key_seed_state_full;
      key_stream_actual_d[2][out_ctr_q * OutputWidth +: OutputWidth] = key_seed_state_partial;
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_key_stream_actual
    if (!rst_ni) begin
      key_stream_actual_q <= '{default: '0};
    end else begin
      key_stream_actual_q <= key_stream_actual_d;
    end
  end

  ///////////////////////////////////////////////
  // Check responses, signal end of simulation //
  ///////////////////////////////////////////////
  logic mismatch;
  always_ff @(posedge clk_i) begin : tb_ctrl
    test_done_o   <= 1'b0;
    test_passed_o <= 1'b1;

    if (out_ctr_q == NumOutputsToCheck[OutCtrWidth-1:0]) begin
      mismatch <= 1'b0;
      for (int i = 0; i < NumInstances; i++) begin
        if (!SkipSeedKeyIvInstance || i > 0) begin
          if (key_stream_expected[NumOutputBitsToCheck-1:0]
              == key_stream_actual_q[i][NumOutputBitsToCheck-1:0]) begin
            $display("\nSUCCESS: Observed key stream of instance %1d matches expected data.", i);
          end else begin
            $display("\nERROR: Obeserved key stream of instance %1d doesn't match expected data.",
                i);
            mismatch <= 1'b1;
          end
        end
      end
      $display("Finishing simulation now.\n");
      test_passed_o <= ~mismatch;
      test_done_o   <= 1'b1;
    end

    if (count_q == 10'd1000) begin
      $display("\nDONE");
      test_done_o <= 1'b1;
    end
  end

  ////////////
  // Bivium //
  ////////////
  // No test vectors seem to be available for Bivium. The 3 instances below are not checked against
  // a known good key stream. It's still useful to instantiate the 3 different Bivium variants for
  // visual inspection, for checking Verilator lint of all three variants, and for inspecting the
  // partial reseed behavior while the primitive is running.

  logic bivium_en, bivium_seed_en;
  logic bivium_seed_done_seed_key_iv;
  logic bivium_seed_done_seed_state_full;
  logic bivium_seed_done_seed_state_partial;
  logic bivium_seed_en_seed_state_partial, bivium_seed_ack_seed_state_partial;
  logic [PartialSeedWidth-1:0] bivium_seed_state_partial;

  // Instantiate DUTs
  prim_trivium #(
    .BiviumVariant(1),
    .OutputWidth  (OutputWidth),
    .SeedType     (SeedTypeKeyIv)
  ) u_prim_bivium_seed_key_iv (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .en_i                (bivium_en),
    .allow_lockup_i      (1'b0),
    .seed_en_i           (bivium_seed_en),
    .seed_done_o         (bivium_seed_done_seed_key_iv),
    .seed_req_o          (),
    .seed_ack_i          (bivium_seed_en),
    .seed_key_i          (seed_key),
    .seed_iv_i           (seed_iv),
    .seed_state_full_i   ('0), // unused
    .seed_state_partial_i('0), // unused

    .key_o(key_seed_key_iv),
    .err_o()
  );

  prim_trivium #(
    .BiviumVariant(1),
    .OutputWidth  (OutputWidth),
    .SeedType     (SeedTypeStateFull)
  ) u_prim_bivium_seed_state_full (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .en_i                (bivium_en),
    .allow_lockup_i      (1'b0),
    .seed_en_i           (bivium_seed_en),
    .seed_done_o         (bivium_seed_done_seed_state_full),
    .seed_req_o          (),
    .seed_ack_i          (bivium_seed_en),
    .seed_key_i          ('0), // unused
    .seed_iv_i           ('0), // unused
    .seed_state_full_i   (seed_state_full[BiviumStateWidth-1:0]),
    .seed_state_partial_i('0), // unused

    .key_o(key_seed_state_full),
    .err_o()
  );

  prim_trivium #(
    .BiviumVariant         (1),
    .OutputWidth           (OutputWidth),
    .StrictLockupProtection(0),
    .SeedType              (SeedTypeStatePartial),
    .PartialSeedWidth      (PartialSeedWidth)
  ) u_prim_bivium_seed_state_partial (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .en_i                (bivium_en),
    .allow_lockup_i      (1'b1),
    .seed_en_i           (bivium_seed_en_seed_state_partial),
    .seed_done_o         (bivium_seed_done_seed_state_partial),
    .seed_req_o          (),
    .seed_ack_i          (bivium_seed_ack_seed_state_partial),
    .seed_key_i          ('0), // unused
    .seed_iv_i           ('0), // unused
    .seed_state_full_i   ('0), // unused
    .seed_state_partial_i(bivium_seed_state_partial),

    .key_o(),
    .err_o()
  );

  // Tracking of seed_done
  logic [NumInstances-1:0] bivium_seed_done_d, bivium_seed_done_q;
  assign bivium_seed_done_d = (bivium_seed_done_q &
      // Clear back to zero upon staring a new reseed operation.
      {NumInstances{~bivium_seed_en}}) |
      // Register finishing of reseed operation.
      {bivium_seed_done_seed_state_partial,
       bivium_seed_done_seed_state_full,
       bivium_seed_done_seed_key_iv};
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_bivium_seed_done
    if (!rst_ni) begin
      bivium_seed_done_q <= '0;
    end else begin
      bivium_seed_done_q <= bivium_seed_done_d;
    end
  end

  // Start the reseed operation right after coming out of reset.
  assign bivium_seed_en = count_q == 10'd1;
  // Start running once all instances have finished the reseed operation.
  assign bivium_en = &bivium_seed_done_q;

  // The last instance is handled separately:
  // First, we put the Bivium primitive into an all-zero state. Then, a single PartialSeedWidth
  // seed is provided while the primitive is running. This allows inpsecting the diffusion pattern
  // of the primitive (depending on the OutputWidth).

  // Register to latch counter value when initial reseed operation finishes. This depends on
  // PartialSeedWidth and OutputWidth.
  logic [CountWidth-1:0] count_seed_done_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_count_seed_done
    if (!rst_ni) begin
      count_seed_done_q <= '0;
    end else if (&bivium_seed_done_q && count_seed_done_q == '0) begin
      count_seed_done_q <= count_q;
    end
  end

  assign bivium_seed_en_seed_state_partial = bivium_seed_en ||
      ((count_seed_done_q != 0) && (count_q >= count_seed_done_q + 10'd1));
  assign bivium_seed_ack_seed_state_partial =
      ((count_q >= 10'd1) && (count_q < 10'd1 + BiviumNumStateParts[CountWidth-1:0])) ||
      bivium_seed_en_seed_state_partial;
  assign bivium_seed_state_partial = &bivium_seed_done_q ? '1 : '0;

endmodule
