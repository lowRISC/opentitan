// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package prim_sha2_pkg;

  localparam int NumRound256 = 64;   // SHA-224, SHA-256
  localparam int NumRound512 = 80;   // SHA-512, SHA-384

  typedef logic [31:0] sha_word32_t;
  typedef logic [63:0] sha_word64_t;

  localparam int WordByte32 = $bits(sha_word32_t)/8;
  localparam int WordByte64 = $bits(sha_word64_t)/8;

  typedef struct packed {
    sha_word32_t           data;
    logic [WordByte32-1:0] mask; // 4 mask bits: to mask off bytes if this is not word-aligned
                                 // set to all-1 for word-aligned input
  } sha_fifo32_t;

  typedef struct packed {
    sha_word64_t           data;
    logic [WordByte64-1:0] mask; // 8 mask bits: to mask off bytes if this is not word-aligned
                                 // set to all-1 for word-aligned input
  } sha_fifo64_t;

  typedef enum logic [1:0] {
    None,
    SHA2_256,
    SHA2_384,
    SHA2_512
  } digest_mode_e;

  localparam sha_word32_t InitHash_256 [8]= '{
    32'h 6a09_e667, 32'h bb67_ae85, 32'h 3c6e_f372, 32'h a54f_f53a,
    32'h 510e_527f, 32'h 9b05_688c, 32'h 1f83_d9ab, 32'h 5be0_cd19
  };

  localparam sha_word64_t InitHash_384 [8]= '{
    64'h cbbb_9d5d_c105_9ed8, 64'h 629a_292a_367c_d507, 64'h 9159_015a_3070_dd17,
    64'h 152f_ecd8_f70e_5939, 64'h 6733_2667_ffc0_0b31, 64'h 8eb4_4a87_6858_1511,
    64'h db0c_2e0d_64f9_8fa7, 64'h 47b5_481d_befa_4fa4
  };

  localparam sha_word64_t InitHash_512 [8]= '{
    64'h 6a09_e667_f3bc_c908, 64'h bb67_ae85_84ca_a73b, 64'h 3c6e_f372_fe94_f82b,
    64'h a54f_f53a_5f1d_36f1, 64'h 510e_527f_ade6_82d1, 64'h 9b05_688c_2b3e_6c1f,
    64'h 1f83_d9ab_fb41_bd6b, 64'h 5be0_cd19_137e_2179
  };

  // SHA-256 constants
  localparam sha_word32_t CubicRootPrime256 [NumRound256] = '{
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

  // SHA-512/SHA-384 constants
  localparam sha_word64_t CubicRootPrime512 [NumRound512] = '{
    64'h 428a_2f98_d728_ae22, 64'h 7137_4491_23ef_65cd, 64'h b5c0_fbcf_ec4d_3b2f,
    64'h e9b5_dba5_8189_dbbc, 64'h 3956_c25b_f348_b538, 64'h 59f1_11f1_b605_d019,
    64'h 923f_82a4_af19_4f9b, 64'h ab1c_5ed5_da6d_8118, 64'h d807_aa98_a303_0242,
    64'h 1283_5b01_4570_6fbe, 64'h 2431_85be_4ee4_b28c, 64'h 550c_7dc3_d5ff_b4e2,
    64'h 72be_5d74_f27b_896f, 64'h 80de_b1fe_3b16_96b1, 64'h 9bdc_06a7_25c7_1235,
    64'h c19b_f174_cf69_2694, 64'h e49b_69c1_9ef1_4ad2, 64'h efbe_4786_384f_25e3,
    64'h 0fc1_9dc6_8b8c_d5b5, 64'h 240c_a1cc_77ac_9c65, 64'h 2de9_2c6f_592b_0275,
    64'h 4a74_84aa_6ea6_e483, 64'h 5cb0_a9dc_bd41_fbd4, 64'h 76f9_88da_8311_53b5,
    64'h 983e_5152_ee66_dfab, 64'h a831_c66d_2db4_3210, 64'h b003_27c8_98fb_213f,
    64'h bf59_7fc7_beef_0ee4, 64'h c6e0_0bf3_3da8_8fc2, 64'h d5a7_9147_930a_a725,
    64'h 06ca_6351_e003_826f, 64'h 1429_2967_0a0e_6e70, 64'h 27b7_0a85_46d2_2ffc,
    64'h 2e1b_2138_5c26_c926, 64'h 4d2c_6dfc_5ac4_2aed, 64'h 5338_0d13_9d95_b3df,
    64'h 650a_7354_8baf_63de, 64'h 766a_0abb_3c77_b2a8, 64'h 81c2_c92e_47ed_aee6,
    64'h 9272_2c85_1482_353b, 64'h a2bf_e8a1_4cf1_0364, 64'h a81a_664b_bc42_3001,
    64'h c24b_8b70_d0f8_9791, 64'h c76c_51a3_0654_be30, 64'h d192_e819_d6ef_5218,
    64'h d699_0624_5565_a910, 64'h f40e_3585_5771_202a, 64'h 106a_a070_32bb_d1b8,
    64'h 19a4_c116_b8d2_d0c8, 64'h 1e37_6c08_5141_ab53, 64'h 2748_774c_df8e_eb99,
    64'h 34b0_bcb5_e19b_48a8, 64'h 391c_0cb3_c5c9_5a63, 64'h 4ed8_aa4a_e341_8acb,
    64'h 5b9c_ca4f_7763_e373, 64'h 682e_6ff3_d6b2_b8a3, 64'h 748f_82ee_5def_b2fc,
    64'h 78a5_636f_4317_2f60, 64'h 84c8_7814_a1f0_ab72, 64'h 8cc7_0208_1a64_39ec,
    64'h 90be_fffa_2363_1e28, 64'h a450_6ceb_de82_bde9, 64'h bef9_a3f7_b2c6_7915,
    64'h c671_78f2_e372_532b, 64'h ca27_3ece_ea26_619c, 64'h d186_b8c7_21c0_c207,
    64'h eada_7dd6_cde0_eb1e, 64'h f57d_4f7f_ee6e_d178, 64'h 06f0_67aa_7217_6fba,
    64'h 0a63_7dc5_a2c8_98a6, 64'h 113f_9804_bef9_0dae, 64'h 1b71_0b35_131c_471b,
    64'h 28db_77f5_2304_7d84, 64'h 32ca_ab7b_40c7_2493, 64'h 3c9e_be0a_15c9_bebc,
    64'h 431d_67c4_9c10_0d4c, 64'h 4cc5_d4be_cb3e_42b6, 64'h 597f_299c_fc65_7e2a,
    64'h 5fcb_6fab_3ad6_faec, 64'h 6c44_198c_4a47_5817
  };

  function automatic sha_word32_t conv_endian32(input sha_word32_t v, input logic swap);
    sha_word32_t conv_data = {<<8{v}};
    conv_endian32 = (swap) ? conv_data : v;
  endfunction : conv_endian32

  function automatic sha_word64_t conv_endian64(input sha_word64_t v, input logic swap);
    sha_word64_t conv_data = {<<8{v}};
    conv_endian64 = (swap) ? conv_data : v;
  endfunction : conv_endian64

  function automatic sha_word32_t rotr32(input sha_word32_t v, input integer amt);
    rotr32 = (v >> amt) | (v << (32-amt));
  endfunction : rotr32

  function automatic sha_word64_t rotr64(input sha_word64_t v, input integer amt);
    rotr64 = (v >> amt) | (v << (64-amt));
  endfunction : rotr64

  function automatic sha_word32_t shiftr32(input sha_word32_t v, input integer amt);
    shiftr32 = (v >> amt);
  endfunction : shiftr32

  function automatic sha_word64_t shiftr64(input sha_word64_t v, input integer amt);
    shiftr64 = (v >> amt);
  endfunction : shiftr64

  // compression function for SHA-256 in multi-mode configuration
  function automatic sha_word64_t [7:0] compress_multi_256(input sha_word32_t w,
                                                           input sha_word32_t k,
                                                           input sha_word64_t [7:0] h_i);
    // as input: takes 64-bit word hash vector, 32-bit slice of w[0] and 32-bit constant
    automatic sha_word32_t sigma_0, sigma_1, ch, maj, temp1, temp2;

    sigma_1 = rotr32(h_i[4][31:0], 6) ^ rotr32(h_i[4][31:0], 11) ^ rotr32(h_i[4][31:0], 25);
    ch = (h_i[4][31:0] & h_i[5][31:0]) ^ (~h_i[4][31:0] & h_i[6][31:0]);
    temp1 = (h_i[7][31:0] + sigma_1 + ch + k + w);
    sigma_0 = rotr32(h_i[0][31:0], 2) ^ rotr32(h_i[0][31:0], 13) ^ rotr32(h_i[0][31:0], 22);
    maj = (h_i[0][31:0] & h_i[1][31:0]) ^ (h_i[0][31:0] & h_i[2][31:0]) ^
          (h_i[1][31:0] & h_i[2][31:0]);
    temp2 = (sigma_0 + maj);

    // 32-bit zero padding to complete 64-bit words of hash vector for output
    compress_multi_256[7] = {32'b0, h_i[6][31:0]};          // h = g
    compress_multi_256[6] = {32'b0, h_i[5][31:0]};          // g = f
    compress_multi_256[5] = {32'b0, h_i[4][31:0]};          // f = e
    compress_multi_256[4] = {32'b0, h_i[3][31:0] + temp1};  // e = (d + temp1)
    compress_multi_256[3] = {32'b0, h_i[2][31:0]};          // d = c
    compress_multi_256[2] = {32'b0, h_i[1][31:0]};          // c = b
    compress_multi_256[1] = {32'b0, h_i[0][31:0]};          // b = a
    compress_multi_256[0] = {32'b0, (temp1 + temp2)};       // a = (temp1 + temp2)
  endfunction : compress_multi_256

  // compression function for SHA-256 in 256-only configuration
  function automatic sha_word32_t [7:0] compress_256(input sha_word32_t w,
                                                     input sha_word32_t k,
                                                     input sha_word32_t [7:0] h_i);
    automatic sha_word32_t sigma_0, sigma_1, ch, maj, temp1, temp2;

    sigma_1 = rotr32(h_i[4], 6) ^ rotr32(h_i[4], 11) ^ rotr32(h_i[4], 25);
    ch = (h_i[4] & h_i[5]) ^ (~h_i[4] & h_i[6]);
    temp1 = (h_i[7] + sigma_1 + ch + k + w);
    sigma_0 = rotr32(h_i[0], 2) ^ rotr32(h_i[0], 13) ^ rotr32(h_i[0], 22);
    maj = (h_i[0] & h_i[1]) ^ (h_i[0] & h_i[2]) ^
          (h_i[1] & h_i[2]);
    temp2 = (sigma_0 + maj);

    compress_256[7] = h_i[6];          // h = g
    compress_256[6] = h_i[5];          // g = f
    compress_256[5] = h_i[4];          // f = e
    compress_256[4] = h_i[3] + temp1;  // e = (d + temp1)
    compress_256[3] = h_i[2];          // d = c
    compress_256[2] = h_i[1];          // c = b
    compress_256[1] = h_i[0];          // b = a
    compress_256[0] = temp1 + temp2;       // a = (temp1 + temp2)
  endfunction : compress_256

  // compression function for SHA-512/384
  function automatic sha_word64_t [7:0] compress_512(input sha_word64_t w,
                                                     input sha_word64_t k,
                                                     input sha_word64_t [7:0] h_i);
    automatic sha_word64_t sigma_0, sigma_1, ch, maj, temp1, temp2;

    sigma_1 = rotr64(h_i[4], 14) ^ rotr64(h_i[4], 18) ^ rotr64(h_i[4], 41);
    ch = (h_i[4] & h_i[5]) ^ (~h_i[4] & h_i[6]);
    temp1 = (h_i[7] + sigma_1 + ch + k + w);
    sigma_0 = rotr64(h_i[0], 28) ^ rotr64(h_i[0], 34) ^ rotr64(h_i[0], 39);
    maj = (h_i[0] & h_i[1]) ^ (h_i[0] & h_i[2]) ^ (h_i[1] & h_i[2]);
    temp2 = (sigma_0 + maj);

    compress_512[7] = h_i[6];          // h = g
    compress_512[6] = h_i[5];          // g = f
    compress_512[5] = h_i[4];          // f = e
    compress_512[4] = h_i[3] + temp1;  // e = (d + temp1)
    compress_512[3] = h_i[2];          // d = c
    compress_512[2] = h_i[1];          // c = b
    compress_512[1] = h_i[0];          // b = a
    compress_512[0] = (temp1 + temp2); // a = (temp1 + temp2)
  endfunction : compress_512

  function automatic sha_word32_t calc_w_256(input sha_word32_t w_0,
                                             input sha_word32_t w_1,
                                             input sha_word32_t w_9,
                                             input sha_word32_t w_14);
    automatic sha_word32_t sum0, sum1;
    sum0 = rotr32(w_1,   7) ^ rotr32(w_1,  18) ^ shiftr32(w_1,   3);
    sum1 = rotr32(w_14, 17) ^ rotr32(w_14, 19) ^ shiftr32(w_14, 10);
    calc_w_256 = w_0 + sum0 + w_9 + sum1;
  endfunction : calc_w_256

  function automatic sha_word64_t calc_w_512(input sha_word64_t w_0,
                                             input sha_word64_t w_1,
                                             input sha_word64_t w_9,
                                             input sha_word64_t w_14);
    automatic sha_word64_t sum0, sum1;
    sum0 = rotr64(w_1,   1) ^ rotr64(w_1,  8) ^ shiftr64(w_1,   7);
    sum1 = rotr64(w_14, 19) ^ rotr64(w_14, 61) ^ shiftr64(w_14, 6);
    calc_w_512 = w_0 + sum0 + w_9 + sum1;
  endfunction : calc_w_512

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

endpackage : prim_sha2_pkg
