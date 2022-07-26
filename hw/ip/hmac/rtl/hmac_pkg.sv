// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package hmac_pkg;

  localparam int MsgFifoDepth = 16;

  localparam int NumRound = 64;   // SHA-224, SHA-256

  typedef logic [31:0] sha_word_t;
  localparam int WordByte = $bits(sha_word_t)/8;

  typedef struct packed {
    sha_word_t           data;
    logic [WordByte-1:0] mask;
  } sha_fifo_t;


  localparam sha_word_t InitHash [8]= '{
    32'h 6a09_e667, 32'h bb67_ae85, 32'h 3c6e_f372, 32'h a54f_f53a,
    32'h 510e_527f, 32'h 9b05_688c, 32'h 1f83_d9ab, 32'h 5be0_cd19
  };

  localparam sha_word_t CubicRootPrime [64] = '{
    32'h 428a_2f98, 32'h 7137_4491, 32'h b5c0_fbcf, 32'h e9b5_dba5,
    32'h 3956_c25b, 32'h 59f1_11f1, 32'h 923f_82a4, 32'h ab1c_5ed5,
    32'h d807_aa98, 32'h 1283_5b01, 32'h 2431_85be, 32'h 550c_7dc3,
    32'h 72be_5d74, 32'h 80de_b1fe, 32'h 9bdc_06a7, 32'h c19b_f174,
    32'h e49b_69c1, 32'h efbe_4786, 32'h 0fc1_9dc6, 32'h 240c_a1cc,
    32'h 2de9_2c6f, 32'h 4a74_84aa, 32'h 5cb0_a9dc, 32'h 76f9_88da,
    32'h 983e_5152, 32'h a831_c66d, 32'h b003_27c8, 32'h bf59_7fc7,
    32'h c6e0_0bf3, 32'h d5a7_9147, 32'h 06ca_6351, 32'h 1429_2967,
    32'h 27b7_0a85, 32'h 2e1b_2138, 32'h 4d2c_6dfc, 32'h 5338_0d13,
    32'h 650a_7354, 32'h 766a_0abb, 32'h 81c2_c92e, 32'h 9272_2c85,
    32'h a2bf_e8a1, 32'h a81a_664b, 32'h c24b_8b70, 32'h c76c_51a3,
    32'h d192_e819, 32'h d699_0624, 32'h f40e_3585, 32'h 106a_a070,
    32'h 19a4_c116, 32'h 1e37_6c08, 32'h 2748_774c, 32'h 34b0_bcb5,
    32'h 391c_0cb3, 32'h 4ed8_aa4a, 32'h 5b9c_ca4f, 32'h 682e_6ff3,
    32'h 748f_82ee, 32'h 78a5_636f, 32'h 84c8_7814, 32'h 8cc7_0208,
    32'h 90be_fffa, 32'h a450_6ceb, 32'h bef9_a3f7, 32'h c671_78f2
  };

  function automatic sha_word_t conv_endian( input sha_word_t v, input logic swap);
    sha_word_t conv_data = {<<8{v}};
    conv_endian = (swap) ? conv_data : v ;
  endfunction : conv_endian

  function automatic sha_word_t rotr( input sha_word_t v , input int amt );
    rotr = (v >> amt) | (v << (32-amt));
  endfunction : rotr

  function automatic sha_word_t shiftr( input sha_word_t v, input int amt );
    shiftr = (v >> amt);
  endfunction : shiftr

  function automatic sha_word_t [7:0] compress( input sha_word_t w, input sha_word_t k,
                                                input sha_word_t [7:0] h_i);
    automatic sha_word_t sigma_0, sigma_1, ch, maj, temp1, temp2;

    sigma_1 = rotr(h_i[4], 6) ^ rotr(h_i[4], 11) ^ rotr(h_i[4], 25);
    ch = (h_i[4] & h_i[5]) ^ (~h_i[4] & h_i[6]);
    temp1 = (h_i[7] + sigma_1 + ch + k + w);
    sigma_0 = rotr(h_i[0], 2) ^ rotr(h_i[0], 13) ^ rotr(h_i[0], 22);
    maj = (h_i[0] & h_i[1]) ^ (h_i[0] & h_i[2]) ^ (h_i[1] & h_i[2]);
    temp2 = (sigma_0 + maj);

    compress[7] = h_i[6];          // h = g
    compress[6] = h_i[5];          // g = f
    compress[5] = h_i[4];          // f = e
    compress[4] = h_i[3] + temp1;  // e = (d + temp1)
    compress[3] = h_i[2];          // d = c
    compress[2] = h_i[1];          // c = b
    compress[1] = h_i[0];          // b = a
    compress[0] = (temp1 + temp2); // a = (temp1 + temp2)
  endfunction : compress

  function automatic sha_word_t calc_w(input sha_word_t w_0,
                                       input sha_word_t w_1,
                                       input sha_word_t w_9,
                                       input sha_word_t w_14);
    automatic sha_word_t sum0, sum1;
    sum0 = rotr(w_1,   7) ^ rotr(w_1,  18) ^ shiftr(w_1,   3);
    sum1 = rotr(w_14, 17) ^ rotr(w_14, 19) ^ shiftr(w_14, 10);
    calc_w = w_0 + sum0 + w_9 + sum1;
  endfunction : calc_w

  typedef enum logic [31:0] {
    NoError                    = 32'h 0000_0000,
    // SwPushMsgWhenShaDisabled is not used in this version. The error code is
    // guarded by the HW. HW drops the message write request if `sha_en` is
    // off. eunchan@ left the error code to not corrupt the code sequence.
    // Need to rename to DeprecatedSwPush...
    //
    // Issue #3022
    SwPushMsgWhenShaDisabled   = 32'h 0000_0001,
    SwHashStartWhenShaDisabled = 32'h 0000_0002,
    SwUpdateSecretKeyInProcess = 32'h 0000_0003,
    SwHashStartWhenActive      = 32'h 0000_0004,
    SwPushMsgWhenDisallowed    = 32'h 0000_0005
  } err_code_e;

endpackage : hmac_pkg
