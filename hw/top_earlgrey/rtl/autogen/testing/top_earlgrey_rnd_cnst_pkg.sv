// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
//                -o hw/top_earlgrey/
//
// File is generated based on the following seed configuration:
//   hw/top_earlgrey/data/top_earlgrey_seed.testing.hjson


package top_earlgrey_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // otp_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter otp_ctrl_top_specific_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'h08_93C2774E
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h10D2_DE1A74D9_85C14900_F7668C16_9458C1E4_4506127C_85C22953_A089B0E5
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h809E0A20_F7F979BF_692ECA00_5096081F_E8FFDFE0_C7717540_05214D3F_0CC6B7AA
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey0 = {
    128'hF9089CF2_787C6C14_B7D1A6C0_618E831F
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey1 = {
    128'hC8129E7A_4149BA28_31FE2E9F_B3B2A1D2
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey2 = {
    128'h5254F861_BA80F82B_303DA306_35AA3D3A
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst0 = {
    128'hD82DEDCD_5992C873_952D50C5_1D21F7F8
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst1 = {
    128'hEEC8B17C_ECD69840_5B3A0CA2_9BB023A1
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst2 = {
    128'h00077F26_91CA2541_1FFDB94D_43C33BB7
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst3 = {
    128'h0FD3E017_1CF89FBB_6926E445_55B0747B
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV0 = {
    64'h87F0D5EE_2B8B9DB7
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV1 = {
    64'h0F7B70F0_CB345C05
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV2 = {
    64'h21BAC589_DFAD65AC
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV3 = {
    64'hAE8A6546_F21BC8CF
  };

  // OTP invalid partition default for buffered partitions
  parameter logic [16511:0] RndCnstOtpCtrlPartInvDefault = {
    704'({
      320'h1657295871E0F57DBABBA5389FF56CE4E1329D01FA1FCF7943D57B9508A9E8D1FFFEF15C246F62B4,
      384'hED73C3F084F0183C44DF2B2D84DC3249FBC6048325D4C625ECEEC3C7F48DA8CCDD589F9FA43AABA8DC41C649B2F9DCDA
    }),
    704'({
      64'hF5869E6FE18E3952,
      256'hD6DFA79E839B863C691CD750D105D75C8F08D1BDF01BC57AFF34AA4E703FA00F,
      256'h37821F53C04F3AC5AD38AC646B008807961F74D1EF05954A802A757289ECB968,
      128'h3325E3EE89E068352902BF3E572C2F7F
    }),
    704'({
      64'h3849E3836AB57EFA,
      128'h56614CE9709298C27140B30AC91EDD6F,
      256'h54A4A529013A6D3C39BE97BA62B589B9E916298A0649A9A3F635DA665461FD9C,
      256'h64B635C7E0CAEE329DDF84E9BA7366CE4EAE10416F98EE7B793BC40A017D736A
    }),
    320'({
      64'h1E1584FFAD542D,
      128'h9868385384916566880F161290B0A446,
      128'hBC73FF007467C44C76F4B377799D1370
    }),
    128'({
      64'hDF7C4775034D3CC5,
      40'h0, // unallocated space
      8'h69,
      8'h69,
      8'h69
    }),
    576'({
      64'h568B3882C765E3CE,
      256'h175F8287DD7E95A4D3C1C4A25C32887E049ED0676AB1F6572524428A0879D484,
      256'h7AC558751092EBFE7FB39F4903AC0EF874213FA290F7E13E7B043E2CC06839DB
    }),
    320'({
      64'h89689D49CA24BE41,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0
    }),
    3776'({
      64'h9AE243733A860B95,
      256'h0,
      32'h0,
      256'h0,
      32'h0,
      32'h0,
      256'h0,
      32'h0,
      32'h0,
      256'h0,
      32'h0,
      32'h0,
      256'h0,
      32'h0,
      512'h0,
      32'h0,
      512'h0,
      32'h0,
      512'h0,
      32'h0,
      512'h0,
      32'h0
    }),
    5440'({
      64'hF49CFEC2EE84C2C3,
      96'h0, // unallocated space
      768'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      96'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      512'h0,
      128'h0,
      128'h0,
      512'h0,
      2560'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0
    }),
    3328'({
      64'hD28D102FC86A79C6,
      160'h0, // unallocated space
      256'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0,
      1728'h0
    }),
    512'({
      64'hCA0C56D51578715A,
      448'h0
    })
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h378530C1_0DD72477_C47AA0EB_970F1443
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h777AA1F1_0CFC4C0B_23F1629B_563D9A02
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h84E7A0A8_B72BE56F_680BFE20_96B49FED
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hB97CB88F_8F255A4A_DA4FA320_AA882689
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hB418F126_854B3B30_204762F6_6ABE7BA9
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hA5A08E23_68F0015C_5DD01D22_4476F99E_7B20F788_1A36653A_B70B9E07_17C91CFC,
    256'hECA84287_601DD59E_A67B4D27_5E1E94F7_F23E7864_ED285FAF_0C4E421B_EE50CE19,
    256'h6AEC3A50_18111AE4_E618A30D_896AB6C4_AF99E539_88EE06D5_BF24E8A3_DCDAE583,
    256'h223A4D35_36FC08A5_486180D5_B1D1D271_AFB2E79A_8B9A27E5_F1C6F823_935FC036
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hD947A816
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hCB35821C_45E4DA33_5EBE8264_E7F514FE_C1654561
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'h91083A37_DCC78CC1_D36C8183_AC847402
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h230D48F7_327AE074_C125E077_FB3727F4
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'hACF4DCFC_C674EA8E
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'h37E1751D_C914FC0A_16CEADE6_B480F985,
    256'h15C24BDA_E0E25BB2_3233C125_8753D29C_6738B1BB_B3079956_F7FA4221_3CD8A69B
  };

  ////////////////////////////////////////////
  // rram_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlAddrKey = {
    128'h4E6FC7CA_539F552C_B801E72B_FA7C14B7
  };

  // Compile-time random bits for default data key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlDataKey = {
    128'h30EC4CC6_E0D963F8_D3B02804_C41EF937
  };

  // Compile-time random bits for default seeds
  parameter rram_ctrl_pkg::all_seeds_t RndCnstRramCtrlAllSeeds = {
    256'hF6BD4609_F1919A2B_937E8EA7_DB17F31A_DCEBEA4A_3D8F4D3F_97DA771F_F9A7651A,
    256'h7A298096_2AA3F903_BDB8130F_38734924_615AA209_097A39EA_1AACC863_D7B8C1EA
  };

  // Compile-time random bits for initial LFSR seed
  parameter rram_ctrl_pkg::lfsr_seed_t RndCnstRramCtrlLfsrSeed = {
    64'h22D728B8_1CE0868C
  };

  // Compile-time random permutation for LFSR output
  parameter rram_ctrl_pkg::lfsr_perm_t RndCnstRramCtrlLfsrPerm = {
    128'hC2047D1B_5B9A49FC_5998187E_94B1DE8F,
    256'h86F9604D_ACCF443B_0AF32A0D_C1645DD8_8E3E8C88_58AE9500_9F13A543_67DFFAED
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h14AC8E59_659F6157
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h551517CC_7E1396E6_3DA9E69B_66FC6B06,
    256'h2FCE3FA3_6D0F4F3E_2E0B2612_8DD2D9C7_D6E64C35_30501DC8_64299FB2_4220A8E1
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h3E71C3EA_B605DEC8_E525948B_AB542179,
    256'hCB428B98_11A4D6F2_13B90A7F_33301BCF_66D14E3F_C4E55D5A_F07E200D_A84D7B9A
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h715FD2E5,
    256'hCE08ED2B_E44FC390_9F9332BE_08CB044E_236A6C13_87D30DE5_FBE3D6A2_94D164C2
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h7084932E_1983850E_4C724311_6F887400_1434908F_3F257D9B_795F2786_0D175977,
    256'h808E6D3C_0A52020C_4824751C_6C312B9A_2C067662_3A9D5896_8D8A3B94_97984499,
    256'h366A4F32_2F891A82_426B6771_78209513_3741912A_7F6E4505_5A0B6068_04495766,
    256'h33265628_8B103E7A_29648C35_3D1E0703_877E4661_69505D5E_559E0947_12081D5B,
    256'h735C5121_2239234E_301B544B_01187B40_38169F53_0F637C4D_924A1F15_819C2D65
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h18DCB3C7,
    256'hCF280EB8_A91427CE_0112BED9_1C1F8644_2CC82E35_08F46F5E_2F22BFE1_555DE9D3
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h7A4A637E_6D2C2E05,
    256'hD0F86F64_2380484A_DAE0F112_8A48C778_4369CE20_0C6C0C82_295C5E43_51BC45EB,
    256'h426581C0_F1C5ABC8_9A149A28_89A54C58_AFF33880_9E92896D_0628C669_01751103,
    256'hB639F182_587C6932_290FC53A_6F5F5923_F976286D_C38CA039_0774A85A_7F17E9E7,
    256'h0C368927_5A729309_467CB156_A5E6822B_A81B60D9_4B0FF1F8_EA323565_05A0561B,
    256'hA7D79035_A30D40D1_08652D03_EEC840E4_721AFD77_5A26D0B9_52222536_0E2D8C98,
    256'hF6C72ACE_DA9DFB45_0D059E1B_29CC125A_65191360_B863041A_55B96F3A_20729525,
    256'h9D0C4346_C46E9F2B_041FA8F0_B1082C71_A017BAAD_2700A5E1_5E1183E0_E488658B,
    256'hF856BB14_00594C8E_0AA46BC9_246C8BD2_F9E16314_F13DC5BB_B1757550_1BC0FBD4,
    256'h2430129C_4A6AA551_D7610C1C_85D24E19_04D8B366_5A664110_9A9EBE9C_0BEDC459,
    256'h70336C60_07163036_3F555AC4_893F1E1A_D2B6F621_007AC17A_15CD792E_7F73A5F2,
    256'h42135DCC_F224A8AF_D8445D8F_316A874D_5F7A0176_0224A3F1_C5FC91B5_1837044E,
    256'hA0CD6A4C_C7361B02_04B2079F_634AB547_95452937_2D09E289_B814D6D5_497BBC59,
    256'hB106E682_0859DE67_3DAEC235_B530DDCC_35405130_67B6D195_93968C71_9C2B2A98,
    256'h47741494_F0371F18_A7E1FE94_9C925C55_A74F0B35_A4592441_32EF7545_41A6EBB5,
    256'hE2C03235_26A277AA_7575D668_CE7B44EA_CA5A4537_04B26702_2B16A70D_D90E8CBA,
    256'h383DB95D_B1865564_E9861867_85A1880A_9099ADE6_99BE1F9A_F2F3074F_85CB0142,
    256'h1627CB30_F46CE1A7_3D339921_C4869CA1_AABAE9E3_545D2952_AF5B1734_0AC9C387,
    256'hD8163B30_A6E56EB6_C4C5B8BE_4AB6CF75_0C150940_B8C62A58_5829262D_70A066DC,
    256'h8A1E8525_65CD6A6A_5C2515AC_DBBB61E2_2BC02514_7422D165_C1EF6FC0_13BC6D3A,
    256'h6E86701A_A449DC50_5182E5C5_E4FF5709_80CDF05C_B0AAA4C8_9E243BD0_F5BCD57B,
    256'h5ACB2A82_DB9CFA46_19D8DF1E_4411147E_CA841F48_D9B1BC23_48E2CE08_0E598D41,
    256'h40126A51_1A81012A_5C828C20_0746DD8E_5470627E_988E1BE1_581E6B9C_549B79C2,
    256'hB7292F5A_F01A0505_C22281A0_194E12CA_09714C6D_3906DAB1_901A6D60_A1C45635,
    256'h3B20DBC9_3E597322_0B4A122C_E1E2A6FC_83E11050_76075B9B_919E77DF_F2E23E64,
    256'h5E03A838_62519AC5_3A88C4D4_2AE97DCD_D0C1AB43_EB792304_66A8D3F5_53C65206,
    256'h60CA4B5F_3AA81B41_E51A02E1_17DA1B54_4A03B0F5_590B71C9_51948F1C_D3588718,
    256'h9CC5921D_ECB3CC6C_74291D4B_A09ED94C_188B8C16_0C5D4BFA_25BAA616_402FAF9F,
    256'h53359527_EF9A7DF9_72E607EA_8985CF34_8E033CA3_C2B9E693_985A88E6_76981A64,
    256'h08C412E4_9E852D46_B3328487_4627F4E7_2DC219AC_F9C6EC54_12AEB0E7_61EE5D02,
    256'h6ED3B28A_B7D9743A_71832925_1B051000_0A86B879_4EE0107F_836F787C_234D1A8B,
    256'h89C88BA6_C3797CC0_1690A0BB_A6AA43AC_491AA4D0_18D3A2EB_44F51C6A_A0AB0ABD
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h58A0909D,
    256'hA3852CF3_5E3DC04A_E39DE052_BE5BD663_299A01B5_126E1652_CB6C5BBB_31AAB2D3,
    256'h9C6EB677_8350A558_733EDB9B_0A911752_CFE9524A_0F0C6560_3A8F661D_B61EAE4D,
    256'hEC966187_A2C2F673_E79839E7_9F4E34A4_1EDB477C_A459E294_9B6B2833_098B20C2
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h183449E1_9936D522_188AFA71_DCD4F329,
    256'h5F67FD74_1BBB9FBB_B16AF0B7_CA005041_E0D2585F_8EA3C274_12CE68C1_66C9CE9E
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'hD9B68002,
    256'h8DE915A0_51379E8D_37175707_D7713E79_DAC47A1E_4AFFAFB2_04EFD921_99B87DEE
  };

  // Compile-time random permutation applied to the primary URND output, directly after the PRNG and before it is distributed to the rest of the design.
  parameter otbn_pkg::urnd_perm_t RndCnstOtbnUrndPerm = {
    173'h0517_CABD954F_609A2CA0_AC2469BC_FA991C43_95C9E14C,
    256'h9531B608_08A368A1_18C0A6B3_154FF602_C3389A11_3A950ED4_11193009_3E59462C,
    256'h97FBE808_92889BA6_4077639A_6AEF1D74_9B1C2190_6C8028D2_BA006B04_1783FE5B,
    256'h064B0695_7783739B_06E27620_80B1910B_AA977915_1945D636_8546DF1B_ABBD65E8,
    256'h5624EF05_46858D0C_5625B8BC_D69E8432_027536A9_0E8E1285_41E94C70_C27DD136,
    256'h6D041B6B_5BD20D40_8465991E_32C2B986_BA39AD14_946F6984_FE132B99_A8A423B1,
    256'h9365540C_4C5AAB2E_381A01E6_F82B1C08_4810B22E_680B1AC0_4F879899_A43A78B9,
    256'hA90EEF44_E06C62D7_B42FDBB3_D4981960_0937B44C_E6DAB2C4_510C970E_8B2BA243,
    256'h59507466_91E2F382_FDC6A4B9_A6968896_12F5B981_02661EC9_C3C5726C_BB4C6334,
    256'hE74B3041_01B0E012_0B644171_9A244D4E_3D3CAA0F_E49550CD_16C023E1_F2A50D15,
    256'h0CEBA030_E4830738_9C4AA98F_3ECFA908_AC958438_5E0DE097_E4A83D6D_5E15BB57,
    256'hCAD0FC14_7D123514_12EBB943_F10F0D16_56CB9295_E889EECF_88250520_7720FEF6,
    256'hA727C8E8_65B6E12D_93276FB5_27348802_291863B3_A3693553_92D1CB35_88A76891,
    256'hC7E87971_69B93140_17CB5DC2_EA158750_B02EE475_B5231F52_8F4FC0E7_7AB24D5F
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'hFC0CCB65_548D8134_5AE11F99_AAF0A86E_9D7A8CC9_2C955F9A_8E96C576_C77B47AF,
    256'h77DB3586_22B90D10_D22EDC28_809CB7DA_AB785EA5_601A0459_1D338F83_536A14EB,
    256'hD0D4BF16_5C15558A_D3729B90_FEB143D1_E06DC392_E5020F26_69ED7189_46F3F2E7,
    256'h8225E6CD_F123E8EC_940B1901_FFF80556_643A18FB_F4D66B42_933B271E_E42FAD09,
    256'h00CEC166_C0134573_BDD5AE3E_3DD8B8C6_8B79F6D7_4840CAA0_20A65721_4CACCC87,
    256'h759FDFA7_D92AA931_7C39497D_671C2430_62F7584E_744A3FB3_524B9EDE_5DA24F1B,
    256'h6F0AB26C_C2A35191_5BBE4184_36CFE9B0_A137EABA_A4C8C485_1238F9E2_DD08077E,
    256'h03B55061_68EEEF70_290E977F_2B170644_98BCFA11_32BB4DB4_883C2D63_FDB6F5E3
  };

  // Compile-time random permutation for URND permutation in MAI.
  parameter otbn_pkg::mai_urnd_perm_t RndCnstOtbnMaiUrndPerm = {
    173'h0C87_1CF88E8B_690002F3_C7E5E23E_3555C4D7_8F91CC79,
    256'h7747A01D_D2287841_45C48F02_CB5EEF28_B07DB151_AB986293_7A358DE9_337C3CC8,
    256'h24374446_860881DC_5D4E1363_747D3A05_AFD8C8A9_39B70352_651300C9_B9ED50AE,
    256'hA0B414A5_844A7290_8C829A5A_5EB2A860_E05CD76A_C549A221_FBFC945E_1DAB5632,
    256'h513198CA_715555AD_D7627081_1C74020C_4C00331D_B0925590_8C0D2545_186A152E,
    256'h4C11574E_621166FD_192EAC13_87C1BADA_50CE0CC0_4F024AEC_ECEC0207_01D982B8,
    256'hE4E5868C_57D41E10_4A0BF8B4_AE42922E_977870B6_6D7B3119_02CDE683_2EC37F7D,
    256'h15AF9440_C3ED6AF6_C1A25506_700C2652_AC0A3BC8_0D4AFC5E_92B4AE0A_19EE0595,
    256'hF58B8238_37ECE964_AB128A7F_935AA571_2A5B660C_DB3F46C9_6FD51416_AA72B294,
    256'h2006819C_3EF3598C_0D824119_F9BC7A7B_35029528_8915ACEB_1DB1390E_74F5F3AD,
    256'h6E292C5C_CB684728_96CCA50F_08D240DB_93683B5A_13A78F43_44A359DD_2FB224DE,
    256'h2320DCC5_80C9BAB9_E3507B02_649F5360_C92BD4D9_ADC2601C_4D3B184B_350B4E04,
    256'h8191CCA7_083298BD_209F3CBA_5DA5F065_601E2AA5_1F4436F0_98402B84_A46021B4,
    256'h24356D3B_0BB6A014_CDC5EB1D_4ECD160E_8125C1E5_E92F4C90_1AD1AB83_72E620D1
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h1DB31F65_142EB7B8_C86E8552_872DD58F
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'hA618755C_0804A62F
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_dpe_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h9C116109_B0A880BF
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_dpe_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'h02C720F0_41E7285A_A646EAFE_8A439DA7,
    256'hB60C6F50_833D5D25_EB18E1E7_62DA7D6F_D2F6F419_E37C0135_35F3C9E2_06B68254
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_dpe_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'hB64A180D_DBACE514_038C5613_D5D0EFD7_DBE21AE2
  };

  // Compile-time random bits for revision seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h5BB0A6EA_FBBA5ACD_035DD770_0FCF1D48_EBD0513A_F0C164B5_2E884F90_F2E62D13
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'hA5968DE6_32180FF3_215B2623_5F17E733_71B938CC_C209B512_6629C48E_1AB45AD4
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'h6B270C16_8892472F_5072EE3C_A90B34EB_329E9A27_6322CC73_8B91ADDA_A137E6F6
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h37A69A20_1DCA49D7_44A1CB70_17026D90_DC96907F_05BAFD75_1E56126B_50AD5C68
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'hDB4EA7C0_3669D35C_1FBB82FD_BDD0BC15_B52BAA0C_5057CC23_28956934_A178AB4A
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'hE3A7537E_EE6264A3_C067F0AE_8787028B_CC21E3FD_65CCF384_275C1342_2A2D18FB
  };

  // Compile-time random bits for generation seed when hmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHmacSeed = {
    256'h3DA8DE1F_07E850B7_F1BCDB08_CC744A0F_36A428FC_3CC24813_17D64302_5D14CBAC
  };

  // Compile-time random bits as a field entropy alternative seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeFieldEntropySeed = {
    256'hE9276534_C3AFD9BB_620030B2_6306197D_A9B6F314_D782FF5C_AE517B83_BBECD428
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'hD182CC47_61BA188D_D84C8710_0D52E6CE_500195F4_031A37C1_77007340_0F05C664
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'hF9698168_48933729_3EE24E42_5434B908,
    256'hAD83ED89_E532E2C3_B2704095_98650110_9446F3A0_A9AF793B_D3A550E2_C0DEE27B
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h296CE2BB_F63B835A_CC5DA048_7D9D30E5,
    256'h641063D8_78E241CC_07701212_AFFA2BFF_92B10DC6_E323AFFD_519436E0_0287ACA5
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h07D0D167_BC3FEDFD_7B457A92_9BAAB0E7
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hE99F89FD_4683681C_3AA7D0C5_0C1A09B0
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h4A371A24_B6E7A444
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h853207AB_E9F1E49E_246B43FA_43F9AB5F,
    256'h0D5BBD47_8397BA41_F724A0CD_9B1D0053_0A468B76_B98096F0_670D2DF3_A28D5DC4
  };

  ////////////////////////////////////////////
  // sram_ctrl_sec
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlSecSramKey = {
    128'hD4B21FCC_BB3941A9_733037B5_D2E6AE0B
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlSecSramNonce = {
    128'h3DDCB22F_37425DFF_B914EFC9_77D542E7
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlSecLfsrSeed = {
    64'hAE6C414F_7C58CABA
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlSecLfsrPerm = {
    128'hF50FB0B4_91085D97_EA696739_A6E87619,
    256'h1314280F_E8C5892B_CC20DB76_2147DCD4_BC2E54F4_57B3E378_1B32BE63_BA9E0D78
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'hCF6A5979_B019877C
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h59A30EF5_73130B1C_47B66509_A3F24365
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h4FEC4BF9
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h86552A80_517D3533_5BA119D0_967D65E6_DB77609E
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKey = {
    128'h04B22181_7DD0B09F_F3FA9716_0E46DE6A
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonce = {
    64'hC27024CC_987F9028
  };

  ////////////////////////////////////////////
  // sram_ctrl_meta
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMetaSramKey = {
    128'h0F3ABA73_5C0C0214_1374D5A9_637A5E17
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMetaSramNonce = {
    128'hC58D0831_01E7C40F_2EC58930_897B6108
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMetaLfsrSeed = {
    64'h391BE560_E757B29B
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMetaLfsrPerm = {
    128'h1CDDC4B3_391ABC1C_940A30C5_A063DE2D,
    256'hCA8AC523_9F4D181D_888667A6_1025F30B_5BED6D49_EBFBB642_B3265D5F_79F98E34
  };

endpackage : top_earlgrey_rnd_cnst_pkg
