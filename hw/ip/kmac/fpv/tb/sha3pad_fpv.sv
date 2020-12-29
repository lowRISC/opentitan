// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module sha3pad_fpv
  import sha3_pkg::*;
#(
  parameter  bit EnMasking = 0,
  localparam int Share = (EnMasking) ? 2 : 1
) (
  input clk_i,
  input rst_ni,

  // Message interface (FIFO)
  input                       msg_valid_i,
  input        [MsgWidth-1:0] msg_data_i [Share],
  input        [MsgStrbW-1:0] msg_strb_i,         // one masking for shares
  output logic                msg_ready_o,

  // N, S: Used in cSHAKE mode only
  input [NSRegisterSize*8-1:0] ns_data_i, // See kmac_pkg for details

  // configurations
  input sha3_mode_e       mode_i,
  // strength_i is used in bytepad operation. bytepad() is used in cSHAKE only.
  // SHA3, SHAKE doesn't have encode_N,S
  input keccak_strength_e strength_i,

  // control signal
  input start_i,
  input process_i,
  input done_i,

  // Indicator: Status
  output logic absorbed_o
);

  logic                      keccak_valid;
  logic                      keccak_ready;
  logic [KeccakMsgAddrW-1:0] keccak_addr;
  logic [MsgWidth-1:0]       keccak_data [Share];

  logic keccak_run, keccak_complete;

  logic [1599:0] state [Share];

  logic rand_valid, rand_consumed;
  logic [1599:0] rand_data;

  sha3pad #(
    .EnMasking(EnMasking)
  ) u_pad (
    .clk_i,
    .rst_ni,

    .msg_valid_i,
    .msg_data_i,
    .msg_strb_i,
    .msg_ready_o,

    .ns_data_i,

    .keccak_valid_o (keccak_valid),
    .keccak_ready_i (keccak_ready),
    .keccak_addr_o  (keccak_addr),
    .keccak_data_o  (keccak_data),

    .keccak_run_o      (keccak_run),
    .keccak_complete_i (keccak_complete),

    .mode_i,
    .strength_i,

    .start_i,
    .process_i,
    .done_i ,

    .absorbed_o
  );

  keccak_round #(
    .Width     (1600),
    .DInWidth  (MsgWidth),
    .EnMasking (EnMasking)
  ) u_keccak (
    .valid_i    (keccak_valid),
    .ready_o    (keccak_ready),
    .addr_i     (keccak_addr),
    .data_i     (keccak_data),

    .run_i      (keccak_run),
    .complete_o (keccak_complete),

    .rand_valid_i    (rand_valid),
    .rand_data_i     (rand_data),
    .rand_consumed_o (rand_consumed),

    .state_o    (state),

    .clear_i    (done_i),

    .*
  );

  // Test vectors (big-endian)
  // "" (empty string):
  // SHA3-224 6b4e03423667dbb7 3b6e15454f0eb1ab d4597f9a1b078e3f 5b5a6bc7
  // SHA3-256 a7ffc6f8bf1ed766 51c14756a061d662 f580ff4de43b49fa 82d80a4b80f8434a
  // SHA3-384 0c63a75b845e4f7d 01107d852e4c2485 c51a50aaaa94fc61 995e71bbee983a2a
  //          c3713831264adb47 fb6bd1e058d5f004
  // SHA3-512 a69f73cca23a9ac5 c8b567dc185a756e 97c982164fe25859 e0d1dcc1475c80a6
  //          15b2123af1f5f94c 11e3e9402c3ac558 f500199d95b6d3e3 01758586281dcd26
  //
  // "abc" (0x616263) :
  // SHA3-224 e642824c3f8cf24a d09234ee7d3c766f c9a3a5168d0c94ad 73b46fdf
  // SHA3-256 3a985da74fe225b2 045c172d6bd390bd 855f086e3e9d525b 46bfe24511431532
  // SHA3-384 ec01498288516fc9 26459f58e2c6ad8d f9b473cb0fc08c25 96da7cf0e49be4b2
  //          98d88cea927ac7f5 39f1edf228376d25
  // SHA3-512 b751850b1a57168a 5693cd924b6b096e 08f621827444f70d 884f5d0240d2712e
  //          10e116e9192af3c9 1a7ec57647e39340 57340b4cf408d5a5 6592f8274eec53f0
  //
  // "abcdefgh" (0x6162636465666768)
  // SHA3-224 48bf2e8640cffe77 b67c6182a6a47f8b 5af73f60bd204ef3 48371d03
  // SHA3-256 3e2020725a38a48e b3bbf75767f03a22 c6b3f41f459c8313 09b06433ec649779
  // SHA3-384 f4d9fc5e9f44eb87 fe968fc8e4e4691e b1dab6d821fb7755 0b527f71ccfb1ba0
  //          43851bb054f28136 4c44d8541904db5a
  // SHA3-512 c9f25eee75ab4cf9 a8cfd44f4992b282 079b64d94647edbd 88e818e44f701ede
  //          b450818f7272cba7 a20205b3671ce199 1ce9a6d2df8dbad6 e0bb3e50493d7fa7

  `ASSUME(Sha3Mode_A, mode_i == Sha3)
  `ASSUME(KeccakStrength_A, strength_i == L256)

  // If absorbed signal is asserted, sw can complete by asserting `done_o`.

  //`ASSUME(DoneStayZero_A, $rose(absorbed_o) |=> ##3 done_i ##1 !done_i)
  //`ASSUME(DoneStayZeroEnd_A, done_i == 0 throughout (start_i ##[1:$] absorbed_o))
  `ASSUME(DoneControl_a, absorbed_o |=> ##5 done_i )

  // Empty Vector check
  //`ASSUME(EmptyInputVector_A, start_i |=> ##3 process_i , clk_i, !rst_ni)
  //`ASSUME(EmptyInputVectorData_A, msg_valid_i == 1'b 0, clk_i, !rst_ni)

  //`ASSERT(EmptyVector_A, absorbed_o |->
  //  state[0][255:0] == 256'h 4a43_f880_4b0a_d882_fa49_3be4_4dff_80f5_62d6_61a0_5647_c151_66d7_1ebf_f8c6_ffa7,
  //  clk_i, !rst_ni)

  // "abcdefgh"
  //`ASSUME(AbcdefghInputVector_A, start_i |=> !start_i ##2 (msg_valid_i == 1'b1 && msg_data_i[0] == 64'h
  //68676665_64636261 ##1 msg_valid_i == 1'b0) ##1 process_i && $stable(msg_valid_i) ##1 !process_i)
  //`ASSUME(AbcdefghInputMask_A, msg_strb_i == '1)

  //`ASSERT(AbcdefghVector_A, keccak_complete |->
  //256'({<<8{state[0][255:0]}}) == 256'h 3e2020725a38a48e_b3bbf75767f03a22_c6b3f41f459c8313_09b06433ec649779)

  // "abc"
  `ASSUME(AbcInputVector_A, start_i |=> !process_i ##2
    (msg_valid_i == 1'b1 && msg_data_i[0] == 64'h 68676665_64636261
    ##1 msg_valid_i == 1'b0) ##1 process_i && $stable(msg_valid_i)
    ##1 !process_i && $stable(msg_valid_i)
    ##[0:$] $stable(msg_valid_i))
  `ASSUME(AbcInputMask_A, msg_strb_i == 8'b 0000_0111)

  `ASSERT(AbcVector_A, absorbed_o |->
  256'({<<8{state[0][255:0]}}) == 256'h 3a985da74fe225b2_045c172d6bd390bd_855f086e3e9d525b_46bfe24511431532)

endmodule
