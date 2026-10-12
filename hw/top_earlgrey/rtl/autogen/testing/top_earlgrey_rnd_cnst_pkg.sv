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
    40'h42_7B4599F8
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h85E1_180905DA_15371B0D_43C83565_49392663_90180A96_71C688C9_807DD44B
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h818AECE8_773AD6DA_66DB3A3F_E58AC30B_53388938_06975A2F_0DB4A2DA_26A43814
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
    768'({
      64'h0,
      64'hF5869E6FE18E3952,
      256'hD6DFA79E839B863C691CD750D105D75C8F08D1BDF01BC57AFF34AA4E703FA00F,
      256'h37821F53C04F3AC5AD38AC646B008807961F74D1EF05954A802A757289ECB968,
      128'h3325E3EE89E068352902BF3E572C2F7F
    }),
    768'({
      64'h0,
      64'h3849E3836AB57EFA,
      128'h56614CE9709298C27140B30AC91EDD6F,
      256'h54A4A529013A6D3C39BE97BA62B589B9E916298A0649A9A3F635DA665461FD9C,
      256'h64B635C7E0CAEE329DDF84E9BA7366CE4EAE10416F98EE7B793BC40A017D736A
    }),
    384'({
      64'h0,
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
    5376'({
      64'hF49CFEC2EE84C2C3,
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
      64'hD28D102FC86A79C6,
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
      64'hCA0C56D51578715A,
      448'h0
    })
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h8C14809E_0A20F7F9_79BF692E_CA005096
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h081FE8FF_DFE0C771_75400521_4D3F0CC6
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'hB7AA3785_30C10DD7_2477C47A_A0EB970F
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h1443777A_A1F10CFC_4C0B23F1_629B563D
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h9A0284E7_A0A8B72B_E56F680B_FE2096B4
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h9FEDB97C_B88F8F25_5A4ADA4F_A320AA88_2689B418_F126854B_3B302047_62F66ABE,
    256'h7BA9A5A0_8E2368F0_015C5DD0_1D224476_F99E7B20_F7881A36_653AB70B_9E0717C9,
    256'h1CFCECA8_4287601D_D59EA67B_4D275E1E_94F7F23E_7864ED28_5FAF0C4E_421BEE50,
    256'hCE196AEC_3A501811_1AE4E618_A30D896A_B6C4AF99_E53988EE_06D5BF24_E8A3DCDA
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hE583223A
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hBE0FDD20_4F2838AD_B4795C89_19D5D683_3F40F8C9
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'hCBA642CF_8B7D74A6_96F14D83_BC9CBB67
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'h393ECFB1_E7D2F693_38AB42AD_967D0D56
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'h91083A37_DCC78CC1
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'hF0170B18_292EDFAD_69B17478_ABF3AD9D,
    256'h4CD31C5D_A55A860F_6557E642_210A6BE8_EFEF1372_270E5E31_20C801D8_6BF606F4
  };

  ////////////////////////////////////////////
  // rram_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlAddrKey = {
    128'hEEC38908_7D1CB943_EA5A3E4B_4CA72F85
  };

  // Compile-time random bits for default data key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlDataKey = {
    128'h058B3411_4EE9203A_94044E6F_C7CA539F
  };

  // Compile-time random bits for default seeds
  parameter rram_ctrl_pkg::all_seeds_t RndCnstRramCtrlAllSeeds = {
    256'h552CB801_E72BFA7C_14B730EC_4CC6E0D9_63F8D3B0_2804C41E_F937F6BD_4609F191,
    256'h9A2B937E_8EA7DB17_F31ADCEB_EA4A3D8F_4D3F97DA_771FF9A7_651A7A29_80962AA3
  };

  // Compile-time random bits for initial LFSR seed
  parameter rram_ctrl_pkg::lfsr_seed_t RndCnstRramCtrlLfsrSeed = {
    64'hF903BDB8_130F3873
  };

  // Compile-time random permutation for LFSR output
  parameter rram_ctrl_pkg::lfsr_perm_t RndCnstRramCtrlLfsrPerm = {
    128'h42572C0C_589F68CC_5992098F_741E39FF,
    256'h52F75D16_EDEF6CC4_F2FA5503_EA9350D9_E3847D0A_230BBDCA_B18E7BA0_A8598252
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hC766FF86_3C5EC901
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h6DDAA45F_B82E470C_B6128CD0_2DFBE668,
    256'h69403A90_E2513781_24220AFE_1F379D95_BEE7DD7A_3D834772_D331B2B4_B45458F8
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h67CD278A_4A08B1FB_8396FD7B_616DCDC0,
    256'h728ECB87_66100E94_AF369547_D86DA71F_EA3E0F92_8CC2F608_55DC7936_C9181439
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h6A988825,
    256'hE405FFEE_ADCB17A1_9CC2F689_35AE809E_2713B925_0E9B07C9_A1B14586_BDCD973E
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h753A6D8F_8899787A_913F5A9D_6F0A9F86_06246B97_8D308922_2F803456_37420240,
    256'h849E9883_6836543B_77671917_60723C21_1A480E70_58419A2C_1451311B_7B38459B,
    256'h76625705_7D0B5952_95495C33_26744B92_3E612901_35791E07_03947E46_505D5E55,
    256'h8B094712_961D5B39_2E28104C_6E851144_27188E2A_7F257300_0C3D8220_1C668A69,
    256'h168C530F_637C4D4A_1F15812D_65640D87_136C6A23_4E049C32_93904F2B_085F7143
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h30AFE945,
    256'h464CB314_BFB5BDFD_34794F05_85EE9837_0C4E3B72_E289C926_3FCA5148_18DCB3C7
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'hA6D121B1_09200BD5,
    256'h209468CB_0648779A_6DA0F214_39022953_13C6A704_A5FC64E5_F3E04459_2F99BD63,
    256'h2FF09451_8F341063_7CE3AA24_CB1CA571_0B96BF08_5E9F0338_3B38AB61_696F9F63,
    256'h9C4924AE_4327714C_282E37DA_FAB7AAA5_398375DA_681A5535_6B217A29_270FE99A,
    256'h720D4C92_9C345D23_66812A4A_1FE35D44_5351756A_F38D24A3_656D9971_90FE4230,
    256'h5D659C90_28EB16B5_3F9B8E02_F8439F80_38886EBC_6477C9E2_190D40B8_633B6E56,
    256'hF8C4650E_8488DA58_95E52DE3_7AC1FA05_EF1082CA_623AB440_A9D15211_83E7A088,
    256'h344A695F_11015C02_382A46ED_5691D25F_E0713DCF_6890C1BC_0F494245_7E1A66CF,
    256'h11C85DB4_E1004E50_62C11099_1DA59B2A_0DB6A1EF_61801C6B_00D4370C_62AB55EF,
    256'h0461CAD7_748401EA_54C9D54A_CA167E01_4D8A4A70_DB2D8929_7A3D618F_C258785F,
    256'h8103D675_15903142_4399CB11_98863019_90D84852_85782C39_33C892A1_EA5DEE6B,
    256'h18C5A75C_59E1D905_DA7822D0_61137246_8F5D9B31_3ADD35A8_831CD874_0812C81E,
    256'h860D2825_1E5018E2_D09E28B0_E14E46BA_96E53E49_106DBC1C_85BF20E3_DAE12356,
    256'h830DCD7A_6357E15D_55139AC0_71BFAA78_08476D14_94F0371F_17D541EE_601CE25C,
    256'h55BA4F05_E1968EC4_C9FE8D15_0698567A_9A9F1B00_9A94DDBB_5D7559A2_A81513BB,
    256'hA94AF8DC_12C99858_AC5A9B58_C71F32D8_C0F5FBB0_4616BB10_96C67BD2_5686ECC9,
    256'h71EDB81B_01F9E1C5_1BA4F85C_C5542162_E7914F46_95D87053_396A1348_6919EEA0,
    256'hABE68545_C992F035_B17340A3_3C007D55_E3230A64_56EABC14_5B89AF59_E4F750C1,
    256'h50940B8E_1C358582_9022470A_CB6DC8A9_B452565A_9B266245_61C6EECD_74CAF009,
    256'h451D08B4_597098DB_F004EF1B_4E97919C_06A86277_06146BC9_49793FD5_C260335C,
    256'hAFDA78C8_3EC0C71A_2C1E88C2_AEE87789_36E2BA42_30B59693_2A82DA8C_FA4619D8,
    256'hDEB74411_147EBF7D_22D6C6D4_8AE2FA5C_20396595_050049AE_F46A0404_A8C20A27,
    256'h801D1B4A_3051C188_FE58386E_C56079B7_24426DE7_0ADCA4BD_6BBAE954_171B8A06,
    256'h8065384B_2775C531_B2241B3E_BB406905_827C1158_D4EC836F_24F73220_A3A12C62,
    256'h1E2A6F08_3E110507_6075B9B6_59E77DFF_C5E3E645_E03A8386_2519A993_A88C4D42,
    256'h9F737430_6AD0FAB2_48BDD9AA_08FD54EA_94819832_92D7CEAD_06D07946_80B585F6,
    256'h86CA1280_EC055642_DC725465_23C734D6_21C2A731_64877B2C_431B0F0A_4752E827,
    256'hB3930622_D8058317_52F2896E_4985900B_EB37D4CD_6571DBB6_9F7E5CB9_81FAA261,
    256'h73CD2380_CF28F0AE_79A4E616_A2399DA6_06990230_24B927A1_4B51ACCC_A121D189,
    256'hFD39CB70_866B3E70_DB1504AB_AC39D87B_974093B2_8AB7D974_3A718329_251AF810,
    256'h000A86B8_794EEC70_7F8361FC_59346A2E_27222E9B_0DE5F169_0A0BBA6B_1E3AC491,
    256'hAA4D018D_3A2EB44F_51C6AA0A_B0ABD556_FF2F1BD0_8CB82CE1_91C2FB01_09FA903A
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h631439B4,
    256'h3907C31E_40DAE7CC_914E3F18_D067045F_6A5D559E_F83E2746_44E5B104_AF0E4658,
    256'hA0909DA3_852CF35E_3DC04AE3_9DE052BE_5BD66329_9A01B512_6E1652CB_6C5BBB31,
    256'hAAB2D39C_6EB67783_50A55873_3EDB9B0A_911752CF_E9524A0F_0C65603A_8F661DB6
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h92DE845E_CCEA2632_FEC9BE59_0D4E1240,
    256'hFB95741D_0082FC46_17678888_230A6B5F_16DDF47F_A4DF673A_6730A216_25ED3AC7
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'h85B92EFD,
    256'h07B7ADC5_CFECC252_10176BB4_737347A2_EAEEDDC5_518E2E1D_BFA516E8_A695B863
  };

  // Compile-time random permutation applied to the primary URND output, directly after the PRNG and before it is distributed to the rest of the design.
  parameter otbn_pkg::urnd_perm_t RndCnstOtbnUrndPerm = {
    173'h14D8_BA0E422B_073803E2_322CC8D4_22902215_61881AD1,
    256'h5411AA3A_0393E3B2_BC05168A_842A2365_93A62546_13B0D94C_B2A828A2_4601D0AC,
    256'h17462129_A4D146C5_17F1C0A5_9492DB18_28C08609_5E084295_A54349AF_98516000,
    256'hFF7D20A5_F5A53260_CA34501A_C5E6C70B_71DCB7BC_0A424D63_A8FC6E91_332110E4,
    256'hC4A33A4C_8C319A16_C7AAB368_4B622DCB_A50F06BB_F4FD4747_41CFE9A7_C42E2639,
    256'h29242F89_92E2887C_CF1DE0DA_100B7878_2EC88751_2329FBBC_229881B3_41A5555B,
    256'h70CCF8FC_431A43A7_89FA90EE_D9A586C6_34554B1C_5893032C_0138033C_D65B01A4,
    256'h16574485_41D27B1E_AF3D23F6_A84C30B4_EA395C58_AC044B30_F64EBD44_2696972B,
    256'h1A52B304_101B0247_F55EC271_53DD9E21_9429115A_961D54D7_6AC698CA_B25F8148,
    256'hDA857BF5_38347960_8B6096B1_4490C473_00C6CA67_05CBDE78_4F1509AE_AAEAFCCD,
    256'h93368C35_54B7FA7C_1517439D_0E1709D9_DD7084BD_09B35BC4_173DF6B6_8058C44C,
    256'h815A4A84_A09B3683_4DC56B65_061F7B23_9F51F819_1082612C_5F25EA0E_DB44DF08,
    256'hF6038F5B_EE645152_4B52B1B7_578FBAEB_D6CE9C30_BBD3C920_5D62731D_6105A62E,
    256'hB2E92DD8_E3B90D41_938B9BC8_BCB57249_EE043B20_F1E6E207_8BA346FA_0016DB79
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'hC6BDD193_AA591D76_1547F6DD_56A5165C_60CCA0C4_EDC8E38D_1A35A914_832E3D04,
    256'h9B530D43_ADEE9290_FA9DB8D7_77FE0C10_6D69ABE2_E0AFA68B_9FB22C3E_6B715AC1,
    256'hFB0F7AD2_CE5546FF_6AF225C7_23F1CD48_0B190178_DCEC18D5_7B133B27_6E2FEA66,
    256'h0080B705_33C2A722_82D8D3B9_C51FF409_869AF7E4_45FD99D6_5E652642_968A8179,
    256'h89208E57_21E894B1_8775C08F_BA2AAC31_7C39497D_671C2430_F59C584E_744A3FE5,
    256'h4B9EFC5D_A24F1B6F_E96CA351_915B4184_36B3EFB0_A137CBA4_851238F3_C3F80807,
    256'h7E03B5E1_6168CFD0_70F90E97_7F2B17F0_4498BCDB_1132BB4D_B4883C2D_63DEB64C,
    256'h6450EB40_285202D9_DF0A9573_3A5434CA_0672A8DA_1E62AEC9_BE298CE6_BF5FE7D4
  };

  // Compile-time random permutation for URND permutation in MAI.
  parameter otbn_pkg::mai_urnd_perm_t RndCnstOtbnMaiUrndPerm = {
    173'h0CB7_8582549B_A306658B_0235B03E_0B2F58C8_A6382228,
    256'hC30A5014_53109254_62F52151_C757EB40_13FC8E17_035CE00A_E80A0A74_77AB23D8,
    256'hC4C21975_384D215C_A276AC03_E4CAD552_59978383_4D2D7660_1F9B2EE2_4551F04C,
    256'h8C7C1384_0DD662B5_90491838_68A522A9_0462D4AE_3C8F0223_A561588B_7780C5C0,
    256'h4BCCC4ED_199315E4_B340D604_B30F6836_5D4F4333_9ADF2B1D_CB65E0E0_3A385687,
    256'h442C5B14_4621EE52_D22D4DD0_A4854DA5_742DBEB6_CC8165AA_A2A97067_159F6E00,
    256'hC4399489_3380650F_70A30C81_527E4F5F_428842CA_2A705B5F_92D179C9_FE374E9D,
    256'hC9DC40A3_F5D09722_511AA935_0BF94022_6819C15D_16E7E8D8_255F041C_A80911F2,
    256'h54C4F38A_33EF1435_79BEB437_6F419ED6_B8FB147A_F555D35F_C39029C5_AF3E2A4F,
    256'hE3D68225_3E6D0C71_8D4DB5E3_AC4AAAE4_39DF1D6B_714962CA_5B423944_B5952878,
    256'h469206D9_1B41DB68_9D3C7A1A_251ACEEA_ED5D26F1_1906D80C_9B3B9E35_07A9A649,
    256'hF4760C92_A3419AD8_A601C4D3_B184B350_B4E04819_1CCA7083_298BD209_F3CBA5DA,
    256'h5F0603EF_74A3E886_C2130861_2EB48B8C_368486AD_A7616805_35D97AC7_53B34583,
    256'hA0497078_97A6480D_68D5C1B9_731068B7_3073C88C_7054BE97_40F04008_B37E6615
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h7ED5FB23_8388402F_1024267E_80168CD7
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'hD429F6F9_A6FFD99F
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_dpe_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h84E0903C_916B5070
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_dpe_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'h72ECF5B7_DBDE63A7_E53A401A_F3B3EB0E,
    256'h9DCA990F_D6A0C893_9C10B877_48F0A948_5B2F9671_F87D8D18_82445C54_60C92B15
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_dpe_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'h5C8AACA5_17F18EEA_46C16684_3FD5A407_6788736F
  };

  // Compile-time random bits for revision seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h518D44F0_E1829B14_B8F03026_BF6DF011_6AF77D3A_A25C37B1_DDC04F6B_EE51CF42
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h0B870EEB_9465D104_14897AD3_924658CE_5BB0A6EA_FBBA5ACD_035DD770_0FCF1D48
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'hEBD0513A_F0C164B5_2E884F90_F2E62D13_A5968DE6_32180FF3_215B2623_5F17E733
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h71B938CC_C209B512_6629C48E_1AB45AD4_6B270C16_8892472F_5072EE3C_A90B34EB
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h329E9A27_6322CC73_8B91ADDA_A137E6F6_37A69A20_1DCA49D7_44A1CB70_17026D90
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'hDC96907F_05BAFD75_1E56126B_50AD5C68_DB4EA7C0_3669D35C_1FBB82FD_BDD0BC15
  };

  // Compile-time random bits for generation seed when hmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHmacSeed = {
    256'hB52BAA0C_5057CC23_28956934_A178AB4A_E3A7537E_EE6264A3_C067F0AE_8787028B
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'hCC21E3FD_65CCF384_275C1342_2A2D18FB_3DA8DE1F_07E850B7_F1BCDB08_CC744A0F
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h36A428FC_3CC24813_17D64302_5D14CBAC,
    256'hE9276534_C3AFD9BB_620030B2_6306197D_A9B6F314_D782FF5C_AE517B83_BBECD428
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hD182CC47_61BA188D_D84C8710_0D52E6CE,
    256'h500195F4_031A37C1_77007340_0F05C664_F9698168_48933729_3EE24E42_5434B908
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hAD83ED89_E532E2C3_B2704095_98650110
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h9446F3A0_A9AF793B_D3A550E2_C0DEE27B
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h296CE2BB_F63B835A
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'hD9B1A6EF_EA7914EB_ED2C28FD_25AC6C1E,
    256'hEEB4AA07_56553F22_4753F8CA_100D9542_0390AAF0_DDC07F41_E60464C9_DF4A85F3
  };

  ////////////////////////////////////////////
  // sram_ctrl_sec
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlSecSramKey = {
    128'h188F5808_60B8D170_B5B9A247_B228DFD2
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlSecSramNonce = {
    128'h32FE1603_77476658_C8814A96_E3CEC90A
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlSecLfsrSeed = {
    64'hBED0540E_2B91CA1F
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlSecLfsrPerm = {
    128'h293527B5_744F0F58_DDED8784_4AE6640B,
    256'hF22C15F9_6FCB6AD6_37A7103B_8FB0CF98_31F26ABD_6DADC184_98951C03_341A8A4B
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h3A577A4E_CBBDF696
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hFD2CD89C_4A353C1D_17C58A76_6CC797C8
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h0D086D3D
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h2C03C1D8_88AA7479_E6FF9376_259A2CA2_81E7BB1D
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKey = {
    128'hCF6A5979_B019877C_59A30EF5_73130B1C
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonce = {
    64'h47B66509_A3F24365
  };

  ////////////////////////////////////////////
  // sram_ctrl_meta
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMetaSramKey = {
    128'h4FEC4BF9_F323C075_F3BDEE69_BB70285E
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMetaSramNonce = {
    128'h21EE604D_AB43391D_1DF4E9BF_68F8EA94
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMetaLfsrSeed = {
    64'h9EDBB1AC_EE62E2B4
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMetaLfsrPerm = {
    128'h8506EFF1_6FA93524_C7EB3D19_E14C06DB,
    256'h174B3CCF_7B8DE0B7_A17A8EB4_A9329897_1A443FE5_9F57E022_C040B988_AB115E45
  };

endpackage : top_earlgrey_rnd_cnst_pkg
