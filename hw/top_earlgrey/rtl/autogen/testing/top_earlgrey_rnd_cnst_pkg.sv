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
    40'h77_7AA1F10C
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h1831_E1150764_69F30E95_99A05092_DB8D1897_9D648405_E35C2803_D5608093
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'hF66ABE7B_A9A5A08E_2368F001_5C5DD01D_224476F9_9E7B20F7_881A3665_3AB70B9E
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

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey3 = {
    128'h87F0D5EE_2B8B9DB7_D82DEDCD_5992C873
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst0 = {
    128'h0F7B70F0_CB345C05_EEC8B17C_ECD69840
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst1 = {
    128'h21BAC589_DFAD65AC_00077F26_91CA2541
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst2 = {
    128'hAE8A6546_F21BC8CF_0FD3E017_1CF89FBB
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst3 = {
    128'h7AC55875_1092EBFE_7FB39F49_03AC0EF8
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV0 = {
    64'h952D50C5_1D21F7F8
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV1 = {
    64'h5B3A0CA2_9BB023A1
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV2 = {
    64'h1FFDB94D_43C33BB7
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV3 = {
    64'h6926E445_55B0747B
  };

  // OTP invalid partition default for buffered partitions
  parameter logic [17407:0] RndCnstOtpCtrlPartInvDefault = {
    704'({
      320'hF5869E6FE18E395262997F89191D6F2BA73E019FDF0F217FFD525678046C71F4B2959D9D965AF479,
      384'h9AE243733A860B9589689D49CA24BE41568B3882C765E3CEDF7C4775034D3CC5001E1584FFAD542D3849E3836AB57EFA
    }),
    896'({
      64'h0,
      64'hD854345D43D7963A,
      256'hFFFEF15C246F62B4CA0C56D51578715AD28D102FC86A79C6F49CFEC2EE84C2C3,
      256'h1657295871E0F57DBABBA5389FF56CE4E1329D01FA1FCF7943D57B9508A9E8D1,
      256'hFBC6048325D4C625ECEEC3C7F48DA8CCDD589F9FA43AABA8DC41C649B2F9DCDA
    }),
    768'({
      64'h0,
      64'h364B7D4E6F07F89A,
      256'h8F08D1BDF01BC57AFF34AA4E703FA00FED73C3F084F0183C44DF2B2D84DC3249,
      256'h961F74D1EF05954A802A757289ECB968D6DFA79E839B863C691CD750D105D75C,
      128'h37821F53C04F3AC5AD38AC646B008807
    }),
    768'({
      64'h0,
      64'hEE59F638FB0662A2,
      128'h3325E3EE89E068352902BF3E572C2F7F,
      256'hE916298A0649A9A3F635DA665461FD9C56614CE9709298C27140B30AC91EDD6F,
      256'h4EAE10416F98EE7B793BC40A017D736A54A4A529013A6D3C39BE97BA62B589B9
    }),
    384'({
      64'h0,
      64'h1FE53934CAE1D79C,
      128'h64B635C7E0CAEE329DDF84E9BA7366CE,
      128'h9868385384916566880F161290B0A446
    }),
    128'({
      64'hB5A9D2D649202408,
      48'h0, // unallocated space
      8'h69,
      8'h69
    }),
    576'({
      64'hBE770CFD47428325,
      256'h49ED0676AB1F6572524428A0879D484BC73FF007467C44C76F4B377799D1370,
      256'h74213FA290F7E13E7B043E2CC06839DB175F8287DD7E95A4D3C1C4A25C32887E
    }),
    320'({
      64'h215F5CC2AB60A853,
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
      64'h5F9ECE1612DE6FCF,
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
    5376'({
      64'h6B0F944AD5A2CC42,
      32'h0, // unallocated space
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
    3200'({
      64'h9208B6F0158C37CA,
      32'h0, // unallocated space
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
      64'hEB2533EA295276BB,
      448'h0
    })
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h0717C91C_FCECA842_87601DD5_9EA67B4D
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h275E1E94_F7F23E78_64ED285F_AF0C4E42
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h1BEE50CE_196AEC3A_5018111A_E4E618A3
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h0D896AB6_C4AF99E5_3988EE06_D5BF24E8
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hA3DCDAE5_83223A4D_3536FC08_A5486180
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hD5B1D1D2_71AFB2E7_9A8B9A27_E5F1C6F8_23935FC0_36D947A8_160C5A8C_52B505B1,
    256'h0DFDCBA6_42CF8B7D_74A696F1_4D83BC9C_BB67393E_CFB1E7D2_F69338AB_42AD967D,
    256'h0D569108_3A37DCC7_8CC1D36C_8183AC84_7402230D_48F7327A_E074C125_E077FB37,
    256'h27F4ACF4_DCFCC674_EA8E6E69_28D9D910_8840117F_BF54657B_C2D6B0EB_F47E1A2D
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h3A9E39A4
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hBBC7A5CC_456DAA88_F03DFFA1_4364F2C0_08C7276A
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'h2F85058B_34114EE9_203A9404_4E6FC7CA
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h539F552C_B801E72B_FA7C14B7_30EC4CC6
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'hE0D963F8_D3B02804
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'h56DC225E_7EBDED0A_AE696238_A3271BDB,
    256'h5B180542_CC8493B3_0C402B83_77BF67E7_65F13D0F_4861698D_FE4A9A40_91BCD1F1
  };

  ////////////////////////////////////////////
  // rram_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlAddrKey = {
    128'h2BC95920_C536A13C_3B8BBD76_FA5EAA92
  };

  // Compile-time random bits for default data key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlDataKey = {
    128'hC81673C1_0D8AF8A2_32F322B0_0B1B8203
  };

  // Compile-time random bits for default seeds
  parameter rram_ctrl_pkg::all_seeds_t RndCnstRramCtrlAllSeeds = {
    256'hAD7A9C20_C3A078F2_BC02C766_FF863C5E_C901E08C_1456D248_AFB3C633_F1B7701F,
    256'h3461F83D_CE4AB614_AC8E5965_9F615784_8D282308_250BF69F_A743F41A_C87601D5
  };

  // Compile-time random bits for initial LFSR seed
  parameter rram_ctrl_pkg::lfsr_seed_t RndCnstRramCtrlLfsrSeed = {
    64'h17311933_93BAC809
  };

  // Compile-time random permutation for LFSR output
  parameter rram_ctrl_pkg::lfsr_perm_t RndCnstRramCtrlLfsrPerm = {
    128'hB2BDD13D_4DAF0E3F_753988A6_65D90D28,
    256'h803F6A58_69BBE547_CB0E8CC6_8CC55F47_936C9181_E0B802E6_7A84EFC4_9071FB56
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h4D18CD3A_32777CF6
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h8EEF82B5_E1CC3A4F_D5216BD4_A5D01BF5,
    256'h74D2631C_E566CE4B_7103E147_5E03EFCD_B083437A_9E8172AC_126299AD_EA1067CA
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hDAE85B94_18CFB4DD_EBCAFC09_5F16B345,
    256'hD0B95BE2_CAD1C884_F48ECCA1_5E0019EA_503BAA99_9D40D87D_39A44871_75B3C83F
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h4C667DAF,
    256'h93D10853_67C1FFD2_16660A8B_DC0FFA52_FF55AD2D_E2836EED_C72651B3_DD41A60E
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h61948875_7E745472_2153565D_31459E87_5029409D_60013E7B_81469F82_93672038,
    256'h964B6D8D_73257890_4F7C8C62_691C8934_4751800D_32584E8E_1E3D7D08_5B553A2B,
    256'h992C2E2A_8B4A7637_86667771_6E430F0E_0900686A_07140C92_281F1344_391D6406,
    256'h854C4279_277A1A5E_5A970A59_95232257_1816330B_985C2F17_05028A9B_15522D04,
    256'h304D4970_911B7F19_106F8F11_48633F3C_9A41246C_0326655F_36358384_6B123B9C
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'hC44F012F,
    256'h3BAF794D_AE06A85C_0013101F_F789D825_6A0951B9_A4888318_EC5FF924_CC419C51
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h218A6689_D7A8D683,
    256'h46134213_6978FB5E_98F70444_4A45610C_880FA8F7_A801018F_18B54A49_03C53D84,
    256'h99C11948_0D2729E0_FCD351A9_04A9BD32_4B942696_365C29F8_AB650846_F8A18590,
    256'hD091B845_30771477_52C8C2BE_093A2707_21171E18_35F57C6A_AC87C6C2_BA060251,
    256'hCDA318B4_F552B79B_7142E624_99C540AD_41976690_E3A9CE05_8CBF3388_B0089623,
    256'h8FE5FB1A_3B6072F5_B44757F2_4E378FCE_B58AD43B_98A566EF_1C05AC3A_F35A6AD4,
    256'hDC4866CB_E7EEA163_87A4FD4D_5EE2C92E_0C36ADB6_C9B340D2_8A91DDA7_6EE10A0E,
    256'hBAB01C78_FF78CC0A_BED9320D_0AE60BA5_12BC2512_17432AB1_4837CF8A_C02A5C0B,
    256'h01B20D0C_C6DB447F_B91D6201_9FB88A59_B45E1A84_69A2639C_41C70242_29DA70EE,
    256'h7C2D91B7_384F78AE_7576290E_61B755C4_C2C2C08C_9DB2DE82_80D55154_E1BDDB6A,
    256'h63907C07_311A6568_C1890646_8D5CBE02_E18E4992_A02764B1_B293204C_6E198E49,
    256'hE5801CA7_B02A407C_8053894C_28DED57A_3B098226_6436A4E2_73F2B6AC_80F15CD7,
    256'h9B1A09AA_C4432452_4231AD4C_F224A826_1B061DBB_316CC488_8A65AF58_68176B27,
    256'h4ACD6D59_491AF9AF_7B84E495_7935AB73_1CD85DC8_12CAE107_95434A2F_479555BD,
    256'hAD2D09E8_CAEB14F1_D5E1A5BE_6BC1070F_89885BF2_5B3DB172_362B30E4_470D9250,
    256'h14497C51_64DBA4E5_CF8E0716_D6089884_77BD494F_0371F1B6_C4ACDA1D_F625C55B,
    256'h05723C23_55B9D059_2655D04C_C4452150_69C41E1A_A6580327_D26A473B_EFA6B966,
    256'h94DD844E_18AEA663_704B266C_790E3D2B_16A7C2C9_0E8CB718_3DBB2011_85E96FE1,
    256'h561A198D_23687EB4_A20DE749_EB1F9DC2_F2554F85_C7F14216_2A09BCF4_C7C1A935,
    256'h33726868_E921B02A_AB3EE01D_15179275_B4D6C5CD_02818281_F622970C_2A495B87,
    256'h04916E7F_BDAA83DD_43056050_2E9177A8_27E2A5A6_161A3582_041159E0_A463025C,
    256'h595FB60E_94583400_F1B36DD3_85035A5C_D428A335_9DFEB406_7A6D75BD_29C9922A,
    256'h3D69555E_FFBCA832_A82DBF4F_A4619D95_EE944111_47EF1841_F4959B1C_2254966C,
    256'h6080E5C0_14140126_AE23046A_0404ABB9_18829420_07470696_94706269_C10E1101,
    256'h581E71C9_B89B931E_70ADCA4B_D6B6A28E_4162E8A0_68065384_B2A65C53_1BEE41C0,
    256'hF15406BF_582AB115_8D4EC836_F24F9E9C_C882E384_8B387A77_2A5E583E_11050760,
    256'h75B9C359_E77DFF2E_2819CA3E_645E03A8_3862519B_553A88C4_D42B137D_CDD0C1AB,
    256'h43EDD921_3466AB13_F553B692_0660CA4B_5F3B381B_41E51A03_0A17DA1B_F84A038B,
    256'hB5590B71_C951948F_1CD35886_8B9CC592_1DECBDCC_6828291D_4BA09F02_4C188C30,
    256'h160C5D4B_5ED20122_5C666164_02FB95F5_3359527E_BD0029F7_E5CB981F_AA26173C,
    256'hD2380CF2_8F0AE79A_4EB7185A_88E67698_1A6408A6_AD64B927_A14B51AC_CCA121D1,
    256'h89FD39CB_70866B3E_51CB1504_BC2AEB0E_761EF189_7409BB71_43B28AB7_D9743B05
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h03513D3D,
    256'h8EE2EDF2_8359FA77_A22A60B3_D985B92E_FD07B7AD_C5CFECC2_5210176B_B4737347,
    256'hA2EAEEDD_C5518E2E_1DBFA516_E8A695B8_63BCD9B6_80028DE9_15A05137_9E8D3717,
    256'h5707D771_3E79DAC4_7A1E4AFF_AFB204EF_D92199B8_7DEEAF93_9372565A_D92F77EC
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h6BA35990_3825285E_F6408304_6F03AFF5,
    256'h7CB7B229_955937F4_E58029E2_AF09AC2B_A1728C7E_19DFD1CE_D4A78F55_072CF781
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'h9CA4A946,
    256'hF0C292A2_2A31E9E9_45467345_6F801EE6_C4A4039C_C66A7B6F_CBD88EE9_9BEB7593
  };

  // Compile-time random permutation applied to the primary URND output, directly after the PRNG and before it is distributed to the rest of the design.
  parameter otbn_pkg::urnd_perm_t RndCnstOtbnUrndPerm = {
    173'h14A4_CC18FC6A_B726A9C0_62ABEA6A_4053AEE3_407591DC,
    256'h60A85AAA_C481B172_8C478415_D74D75B6_E1D08A91_7FB28420_407474ED_0B0146E3,
    256'hC008FB59_1D131F84_439218B5_915AD93E_0F5846C6_00215449_223EDD0B_454C250F,
    256'h33BF2885_2D431C5D_CA1D44B1_6E6E1304_BA98DD0A_3605E936_5BA9F84E_46525602,
    256'hD869C632_2293B0E1_8467F5DE_D0F604A5_2D928B5D_E4165102_D4647268_70F24908,
    256'h0D0C6B82_C9B00EBC_823CC55F_AA47C339_41393440_18D4F1B1_7C151821_93494543,
    256'hD4967763_AFD56B27_BB806624_C40FE00D_33F5D179_905B2C89_C2486978_946EB73F,
    256'h9BC30C13_94F20E96_953C5211_0598E821_74258D56_D7841BCA_08D740DF_14D14469,
    256'h5E0461AD_4E98E671_CB491452_68BD652E_0B79727A_92198F9E_895660EC_64488E51,
    256'h018DB4C3_B83CD06D_05E9A4C8_0AB10903_0B199F34_169BC1DF_2B2C4FAA_F4667C81,
    256'hD37F5FE0_93E885E4_C8F1602D_38A14753_2E050AAF_2E8D306E_C1454CC4_7300D20A,
    256'h6705CBDE_6376278A_A8426722_B93D6964_DB6E36A9_A549AAA5_A3B7E0A8_BB354070,
    256'hB8A1A76F_69C21559_7B549BCB_4274566B_7882E7B9_03ECE80B_0AC62362_32055D6A,
    256'h1284E136_6D069B8A_D7AAC52D_C77D87BC_C8E7D47D_02EB6591_082612C5_F25DCCED
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'h8CD697A5_B6D242DA_3A46CC86_6EB362B2_7FB5DCA6_AB035CD3_09E3DBA1_3FFFA7A3,
    256'h2CA27180_5578C89A_14190C72_33BBC760_561D5FE0_6B3BB859_774E98FB_88C2AD29,
    256'hF41A23A0_69EDE696_A8AFEB34_08C3999C_18CA44A9_3CF10161_25B92F4B_D9F86395,
    256'h7DC99E6D_9DE98290_811C3707_356A83CD_2854EA7A_1B8A58E8_178FCF11_50C6F97B,
    256'h1FD0C12B_68105DE4_AADDBD27_9370EE2D_ECFA9204_948E496C_3043FE0F_65F0DE06,
    256'hB7AE9B0D_051EDFB4_2EBA8D22_5A154A89_4753E791_163202C4_0BAC74F6_64D78426,
    256'h764FD45E_F7D500EF_0E0A666F_134573F5_5B24D13E_3D12CEB1_52518BBF_79BCCB4D,
    256'h85484041_F320FC57_214C67F2_A4E136BE_87B0D875_9F7EFD38_E2C02AC5_39317CE5
  };

  // Compile-time random permutation for URND permutation in MAI.
  parameter otbn_pkg::mai_urnd_perm_t RndCnstOtbnMaiUrndPerm = {
    173'h1112_1B8F0003_7CB2A410_38959875_348BCFAD_05256D88,
    256'hEE7E85D0_97600853_DC99161D_CFC4D3A9_9BCDBB57_0C012888_DBC00530_D49ED7AE,
    256'h6471CA1D_730F9453_E0A2D500_15B23EB8_B2DF889A_E4ADF086_1722A788_F519A630,
    256'h28AB4325_5837B1BA_EF1F2302_CC6616D9_94E01747_3A245291_FC196352_591A0946,
    256'hCC1104CE_38BDB80E_4D78AB7A_BF6F8E05_A5A1380D_18669169_52D892E7_A31960FB,
    256'h6FAB1865_E8695AFE_B418DA4A_EB54AD06_4B4CB65F_46ACE45C_10A23C38_97100554,
    256'hD910FF75_A438492B_C271364E_6D572A0E_89C20048_11530353_556602A5_AD48AA75,
    256'h209756A8_4CB1AB65_22B63024_22C9ADEA_5D04B88F_8BF1BABC_C945A3B3_6DA4B0CC,
    256'h7A331B66_5F2935D3_B00AF40E_03BE856A_288341E0_624639A0_1765ECDA_43559BB2,
    256'h06C5AACC_525E8524_051DEFEB_A316A90E_8E8C2DCC_F0D2596C_50A88804_2FF0FC4C,
    256'h2AFD4BBC_844663C4_204811B8_59CDE3D3_D9A814A9_445013B6_03ACEC20_E439D697,
    256'hCEB5B8A4_B0A72DA1_1CA255C2_943C2349_0358EDA0_EDFA4C27_4F1E8689_46B3BA9C,
    256'hD149BC46_5500DCC5_80C91650_DCF1A9CC_1D4C9927_DE58324C_25CAC335_6E4C2C61,
    256'hC4D3B2B6_C259A85A_70240C8E_65649C20_CA62F482_7CF2E976_97C19580_78AA947D
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h13981E66_1DD5361E_34E674A6_F46CF90B
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h9DE91FDD_12B9C73D
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_dpe_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h5DCE345B_518D44F0
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_dpe_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'h192ADC91_83E9C157_7BD88AB7_E872B9CA,
    256'h7CED0348_F1FFE2FD_5917A2F0_16650E10_905354EC_357A0E7D_A11BBC93_2E166838
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_dpe_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'h54E9AC49_F0F25190_576DE8E2_5672C13D_DC612FE4
  };

  // Compile-time random bits for revision seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'hEB329E9A_276322CC_738B91AD_DAA137E6_F637A69A_201DCA49_D744A1CB_7017026D
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h90DC9690_7F05BAFD_751E5612_6B50AD5C_68DB4EA7_C03669D3_5C1FBB82_FDBDD0BC
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'h15B52BAA_0C5057CC_23289569_34A178AB_4AE3A753_7EEE6264_A3C067F0_AE878702
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h8BCC21E3_FD65CCF3_84275C13_422A2D18_FB3DA8DE_1F07E850_B7F1BCDB_08CC744A
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h0F36A428_FC3CC248_1317D643_025D14CB_ACE92765_34C3AFD9_BB620030_B2630619
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h7DA9B6F3_14D782FF_5CAE517B_83BBECD4_28D182CC_4761BA18_8DD84C87_100D52E6
  };

  // Compile-time random bits for generation seed when hmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHmacSeed = {
    256'hCE500195_F4031A37_C1770073_400F05C6_64F96981_68489337_293EE24E_425434B9
  };

  // Compile-time random bits as a field entropy alternative seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeFieldEntropySeed = {
    256'h08AD83ED_89E532E2_C3B27040_95986501_109446F3_A0A9AF79_3BD3A550_E2C0DEE2
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'h7B296CE2_BBF63B83_5ACC5DA0_487D9D30_E5641063_D878E241_CC077012_12AFFA2B
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'hFF92B10D_C6E323AF_FD519436_E00287AC,
    256'hA507D0D1_67BC3FED_FD7B457A_929BAAB0_E7E99F89_FD468368_1C3AA7D0_C50C1A09
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hB04A371A_24B6E7A4_4411DE54_8F89387F,
    256'h2D357218_8F580860_B8D170B5_B9A247B2_28DFD232_FE160377_476658C8_814A96E3
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hCEC90ABE_D0540E2B_91CA1F2D_A6A318F2
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hD3FAFFF2_31021D56_8B26F8D4_86E5E705
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h566B6EA0_AA9B1869
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h1888C399_553CD29E_09FF0125_292611E7,
    256'hA59EDE18_9AC67672_7D393BA1_D157DAF2_CF0ABB4D_31CA903A_ECC7B3EF_5B040D60
  };

  ////////////////////////////////////////////
  // sram_ctrl_sec
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlSecSramKey = {
    128'h6CC797C8_0D086D3D_EAC575F5_7CC00756
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlSecSramNonce = {
    128'hA6638934_5E175FDB_6B5AE8C3_AF287203
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlSecLfsrSeed = {
    64'hC69AD866_C581D410
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlSecLfsrPerm = {
    128'h3DB894FC_5EF8DCE0_34DA7A41_82AF2694,
    256'hD5F1FA45_49323BCB_2B0E9D21_24EBF72B_99447084_703A397E_11AC7966_B3D50B58
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h0E46DE6A_C27024CC
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h987F9028_0F3ABA73_5C0C0214_1374D5A9
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h637A5E17
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h4427BAC8_826AA895_EACE19F2_C7DF9E2F_7E030638
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKey = {
    128'h6126AD58_57E86ED2_5A62A45D_97B2DB02
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonce = {
    64'hC985E4E4_61846523
  };

  ////////////////////////////////////////////
  // sram_ctrl_meta
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMetaSramKey = {
    128'h65E8C98F_9F887292_8054B7C1_9D5993EF
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMetaSramNonce = {
    128'hDB9C78AB_30D9525B_3F86FA2E_BC65E81F
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMetaLfsrSeed = {
    64'h1079CBD7_40B8DFE1
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMetaLfsrPerm = {
    128'h95BD06D6_9B6ECF0E_C781EBE1_62371A4C,
    256'hAF3A88C9_F24B1F89_2F723FF4_05243B8A_1F74D103_41117908_FB2A5959_99D81AD7
  };

endpackage : top_earlgrey_rnd_cnst_pkg
