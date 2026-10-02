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
    40'h89_9E1A729D
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h6623_A53DB190_59461110_30421E12_C555E7DA_31C90A48_95E03672_13766023
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h6DA7E1E3_EA6ACC68_AED2A2AE_CDA5C995_BF6460C3_12DCA7F2_3EFB49CD_F174E1C6
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey0 = {
    128'hF20D1097_C5A69C31_0BD88D7D_6C8DE1A2
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey1 = {
    128'h68953171_05EAE6AE_D6112937_1D382D20
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey2 = {
    128'hCADDCD83_8F16A6B4_81B4E775_46EA10AE
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst0 = {
    128'h4C18F97A_5D63D542_31546185_6B0D4E58
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst1 = {
    128'h6A97D70A_3BEB0846_C059BD62_FB03D643
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst2 = {
    128'hCFDB1788_DBD08CBA_33002B9D_35855978
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst3 = {
    128'h885D90F9_DFA09D9E_8406EF4E_90D241F1
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV0 = {
    64'h79AB771F_FC65FC40
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV1 = {
    64'h05F07BEA_9065B020
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV2 = {
    64'h0CDB76DE_D2E48517
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV3 = {
    64'h5C03F84C_75DAA40C
  };

  // OTP invalid partition default for buffered partitions
  parameter logic [16383:0] RndCnstOtpCtrlPartInvDefault = {
    704'({
      320'h27F08A79810AA0FBF23A364293079E58D6B5011D1E98E2E6B7573BAA905CCDDDA2E456A22D5DCAC7,
      384'h6CA246025E3B433419010601FB615CD4B0B07EF1C4639146EB96B57C191663C5E3FDFCF3460E1AA22DA363742FE5FF0
    }),
    704'({
      64'h4892C66B7B76D9D1,
      256'h32CDFBF473A044F26BD25EF7A7E1669CEC42975A361CC4FA43D2521041E0C327,
      256'h9857EE5973EC152FAE65541D94F444121D05FBD874796C34092DDBC5A27A6BF5,
      128'h7701170F9799CB6114613C4F678291BD
    }),
    704'({
      64'h2F0AC8577C7CDB4B,
      128'h16A0BF25A2DFE4FDB75B4ADD2F3F714F,
      256'hCBFC5C8BE12D73D81800BE0D0C8C68F04B1C9D25654DC7265FF3B79B8D5165A8,
      256'h1E450AB5061D9102B2C07177CEDB61778E0DAE9B8C388016EB698F02CB2CA5C1
    }),
    320'({
      64'h90731DD73445EDC0,
      128'h78B1F2592D8B4C1265C52B200E9734E0,
      128'hFB2C9B305140AD8123E2115C8B74D68F
    }),
    128'({
      64'h56AE233E698CBEC8,
      40'h0, // unallocated space
      8'h69,
      8'h69,
      8'h69
    }),
    576'({
      64'hF412E8EE6025EE2F,
      256'h7035EFF712724527BCBDC29BBAC6A198722F32E8C42EA1C0961A7C98D8E75F9F,
      256'h2617CAADF2B4B29AB85960E9F3640A4D2AA88EDA8DFA26761852A1769A94F974
    }),
    320'({
      64'hB2E1AA480B4B3B95,
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
      64'hE79E30B5803CFF41,
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
      64'h41EEC2C1A01AEC9B,
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
    3264'({
      64'h319797EB24FAD6AE,
      96'h0, // unallocated space
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
      64'h16D384F3B8E51823,
      448'h0
    })
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h3BAB3B5D_39966B88_5C2850EC_AFAFEB20
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h28ED881B_51E0F5BA_F5379ACC_38AF26B5
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h86CC26B2_D0C04CF4_7BFD8D04_62BD3EC2
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h7EB9FAEE_5BFF604B_EAF9DEC1_0117ECDF
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hB85E76B2_9B3951BA_1A2EB7C6_A4212F2C
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h17070000_CD4E7F65_52C7BEBC_B9E862A0_2875BACB_B7EB0B3C_3AD9478A_211851D6,
    256'h88F5FF35_6F036DE5_629251C1_F7AF7B05_6D1221CF_FD86EF5D_939D9C19_2B09863F,
    256'hF2B9A0D8_31DA9988_DC1A8CE8_33117C87_7F9916BE_F4426721_E60F291D_9623A715,
    256'h4D6A3DBC_0341E01D_E90EC793_1059D6F1_4D0BB522_8B1B6D59_2A66CA73_6B20EB71
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h761E31B3
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hCDF7212F_AE38CB6F_A91449B5_36C60C27_31503FC1
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetSramKey = {
    128'hBE47E91C_EA4EDC71_3BBE669E_7ADF3048
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetSramNonce = {
    128'hBE1BA3A5_6A28E4A9_8962E03E_9FDA128C
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetLfsrSeed = {
    64'hB88ADF10_24DD17E4
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetLfsrPerm = {
    128'h40B4C3B5_C74C3BA9_7DE0DC07_DA60089C,
    256'hFAB992CA_1A863805_DF4C4249_927B5BC0_72529F9E_BD8CC41A_2D6E46B6_FF7CA5D5
  };

  ////////////////////////////////////////////
  // rram_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlAddrKey = {
    128'h7168DDA2_F6C111B0_D9365127_52E836DA
  };

  // Compile-time random bits for default data key
  parameter rram_ctrl_pkg::rram_key_t RndCnstRramCtrlDataKey = {
    128'hFB2911A8_766442C8_D99B2890_0C304743
  };

  // Compile-time random bits for default seeds
  parameter rram_ctrl_pkg::all_seeds_t RndCnstRramCtrlAllSeeds = {
    256'h75AFB662_6976CE17_00E1F8C9_4978AC9F_F603E651_D468BBD4_142CE398_5BBCF288,
    256'h7108B602_FAB9D760_9E39E3B0_EA8BE77D_B86FAE26_5D31AE15_2A1EF235_E08C1BA8
  };

  // Compile-time random bits for initial LFSR seed
  parameter rram_ctrl_pkg::lfsr_seed_t RndCnstRramCtrlLfsrSeed = {
    64'h28ED7FA1_AEBEB961
  };

  // Compile-time random permutation for LFSR output
  parameter rram_ctrl_pkg::lfsr_perm_t RndCnstRramCtrlLfsrPerm = {
    128'h82ECCB51_676C3380_8F0F5865_5C1A15F1,
    256'hA4C72864_A6237FDE_AED42302_93B267D9_C9170136_7EAE9CBF_18BE6346_F944DEE4
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h03173AE8_3D1417F5
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hB8214088_CAE3F014_DE2E4F8D_BF2A90EC,
    256'h4A5AD0AF_D4D793B3_D8981561_2DC79E1B_487F0457_7386FA1A_CF437599_68C4F5A6
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hBED24CDA_AD6E7F26_E751EED5_40BA51CE,
    256'h6225702A_D73E317D_E81184F2_1DE8E717_60662B00_9384831F_E29A58D4_D83B0D3F
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h96D7ACC9,
    256'hA47AF092_DE8AAFAB_8C30F02E_F79DEAF6_4EFBCCE5_6CAA32C9_18895632_4CA3D98E
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h73128689_256C5A20_6A357B62_675F9C3B_93455B98_8D315D33_844F2F2E_02174B81,
    256'h723D1F41_6E4D9676_941C4354_10272C51_9D872157_68180882_612A3C22_48649558,
    256'h88978C53_56389B26_0E305E8B_4C786339_3A469A8F_59520319_6D55241E_601A9277,
    256'h14717C32_6966367E_8E91285C_6F831650_49470611_130D0A65_1B0B4075_8A058085,
    256'h0C00097F_4A904E44_9F7D2D79_37040F74_7A422301_1D703407_15992B3E_296B3F9E
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h23DDBF0A,
    256'h3035357E_E23994CA_891FCC06_2363E91F_83DD6930_881E853B_48ED6542_29698F6F
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h2E5DE51E_E54C5710,
    256'hFC8A81E8_A6015513_0FF638C4_72A14A02_778FADDC_54CB93A0_B1E54E0F_9921EDE3,
    256'h88E08A2D_3A980207_420552DC_846C44B7_28215293_345CD5F6_5D7618D4_C97454EE,
    256'h4844975A_0F667448_454E3828_89B3AD72_78520396_CBE24270_8C00E67A_AF090182,
    256'hBD26468A_6D28A16B_6C124BB6_D7511CD7_4F71F429_573264D8_AA31ABB0_C8B9B887,
    256'h49C6F5FC_1088F6AE_F79F6E2A_8EB21BAE_390D9E71_1BB2E113_0D457772_10C04497,
    256'hF4E2384C_16813C54_1DF0B034_B101E20D_2A492675_6AA5329A_CB45625C_10214438,
    256'h9ED25C79_2FC76F42_2CEE354E_8159F979_14D5456E_2AB09AC1_76A0D7A5_1B18134F,
    256'h76CC7625_17FAFD79_31493194_F41CEAD7_0711BF6E_75CC41AD_591A68C3_BA26E8AD,
    256'h498FECF8_B62C0B5D_D2601829_DFB085E9_A9C23295_932C8E0B_E94FAB21_9239C04B,
    256'h560A598A_7CD5D827_145DF071_F400B589_11DCA649_CAFBB6C8_4746231D_692CDD10,
    256'h1B082ADB_4988BF16_6A67963D_C02C09DA_1570C870_70317A80_50758436_808A10E6,
    256'h7B8ADAF8_B506D7C2_F20347E4_A28F1C33_900614DE_B0987521_4AB0F0DB_A5661D50,
    256'h40DDBA97_9203F188_4791000A_519C60D9_D54C396C_62A69C0D_9C50A9EB_901AAB1C,
    256'h32A51A62_56D91C83_07506F47_23B1F139_8DA06B82_0FB69187_4E18AE8E_9A263080,
    256'h05C6BE02_AC4B186A_53214158_49D24161_C9AEE660_4E775D29_688D4925_BE5AC787,
    256'hEA582367_F3C07ABE_F1304EB7_7566571C_869E05B5_1538098A_88E29980_6929D0BA,
    256'hB28EC949_CB5907E3_E4CF57C1_F2C05846_8927DD01_8CDA76C9_43959587_C1072DEC,
    256'hC371EF9A_A134656F_6E6F22B2_DF03C665_5A733CDF_42ED6D63_10E68EA4_9181A4F8,
    256'hD64D2EF7_983BC297_245DF537_E5C9C2A9_8CAEC502_0E579525_8DE7B48C_20A6D8A3,
    256'hDE16FE26_C486DAD2_552880B0_F2370959_63AC0C85_C5F36E48_9FAE18F0_46BD9827,
    256'h59370F5C_9B1654A4_1598E5E0_572914EE_EE7C4742_D1230292_B15554A3_926AE1E2,
    256'hBC0634FD_89064801_7A6D375A_52848476_6FC100B6_0444EB4C_D2280FB7_3CE4A7B0,
    256'hE3C5FF65_4D827ECB_65D44AA0_5393E220_BEF186EA_A930175E_266259DB_7D9A12F6,
    256'h7242424C_1AB9B059_FA22BB05_906A35C6_984693AA_B3A1E95A_87160044_32317EA7,
    256'hC0DBF8BE_08A6F831_30C6635B_FC12A761_F1850396_6450A121_3F83AC0D_14912242,
    256'h919B26A7_9420F54D_4FA810ED_B36D56C0_091A9339_F1361C12_2C6D0DA0_41085916,
    256'h7B1AE662_2F1431A1_3CF23BDA_D19DB520_9FE8804A_A30818A2_343344B7_3111BAA2,
    256'h7B258F4B_08843D61_59710B41_E8169123_190C34E9_742CC86C_5BC62C9B_0ACFD9B0,
    256'h075EE637_C99996DA_4C3C03A1_AF31C6AB_050F896A_646A1835_0941B524_73423A73,
    256'hAAFBAEDE_C5C2E672_6909C9D9_A0339404_5BE4AE4B_AA07B586_9062976B_0B879B7A,
    256'h89B66686_4BD46C01_16A36702_651A9642_57886981_755B97C7_FC15F859_E251ACCC
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h3AB9C364,
    256'h26557C5E_30938DDF_31172D2B_6246EC02_3127B2B9_DBAF000D_63D00166_A5380089,
    256'hE4A1CB52_B7E19D11_E59AD669_C0425DDA_E509854F_A21B6C22_78CDE0D7_A9E6769D,
    256'h6832770C_25E48FD3_47814D55_8C7AC1EF_79B30FFB_E8446567_73C35908_5FE7C6FA
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h7A2753FD_5CA67EA2_476C80C1_A642EC44,
    256'h21A0E713_529F48F5_70ABD742_8DAD8701_6E978DCF_01ACD858_E304F99E_FDAFC53A
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    32'hDBF3BFA3,
    256'h150C00B2_0A89DB4F_80508919_932DC590_90A537F7_134A9C93_20BA5A8F_4453C481
  };

  // Compile-time random permutation applied to the primary URND output, directly after the PRNG and before it is distributed to the rest of the design.
  parameter otbn_pkg::urnd_perm_t RndCnstOtbnUrndPerm = {
    173'h0A84_D8847731_AA5B1902_B2CB50BA_F8B7CAC2_8CC505D6,
    256'h36486B46_AF0E879C_629A044F_B4D0C2FA_F1718B33_26B8D8EB_D871D851_6B0B8144,
    256'hAAFB02F9_6D2FBE45_DB0E0860_2460414E_3D82400A_1A84D4B2_4F2ADB43_79856CCA,
    256'hBAC180E6_5207E4BA_E7228351_EE01A74D_E4FE64AC_AF2BA9A7_6D487511_5DD5C546,
    256'hC79570D0_B8A8B3E1_03DA7372_BE313145_A6F0F012_D60F746F_A010A781_244F0275,
    256'h653BEFCE_A24DEEFA_1170A5CF_31D2832D_022253B6_D20D1A4A_DEE2F4B4_4ED9298B,
    256'hD4B1AAEC_259C2726_71398D3A_BF81C146_9151FC11_9D2A1910_9A0B96F1_C50EF022,
    256'hC7030930_D962E526_253E66B4_C9ECFE4E_7B8930C2_0E6712CC_B64F368C_F04663A3,
    256'hD66D80BB_A129F234_5871FF14_A2C24FA4_E511A6C8_D20A8391_8C2221C9_0406AB2B,
    256'h8A8082D5_FE208D6C_C088F695_8D02856D_3D02E716_A9A59948_F10F8F91_03845584,
    256'hAE77608B_63E160CA_A8F80A37_554A4B4A_D494874A_449AE5A5_6061CCBF_0B1E52D8,
    256'h08E548BA_C6FEA21F_89901234_85F4E794_A6546408_559D1EEB_4A3BAC49_54B2B188,
    256'hA51C9BCA_61E49146_7D249D46_6910D038_99F60109_9806B531_1D0458B0_06B18530,
    256'h0668D9C9_58A35B84_15072CF1_EE617EB7_41F652F0_755B7648_A99AE554_1C7A5184
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'h9E4B560D_1A3620A5_F4A45E2D_8A2338D6_058FC340_AB0C6EAE_D97712BD_2651A713,
    256'hB519903A_DC4829DA_61826AB6_4C709BCE_66476827_A153E7FB_5B78D1DF_91D5F107,
    256'hB36CD824_FCED4DCF_ADFAD709_BE57E097_5D08F70F_2C282ECB_F68E6FE2_E3A655C6,
    256'h8BC217F2_43CDA93C_74E15287_5C81E5D4_63325FD0_E67A851F_72B179B2_3976A046,
    256'h7C411C7B_FE253EC7_9549E4AC_2B98F571_86FF2A15_FD22A8D3_442167CC_01038435,
    256'hCA94DE16_59F92FC8_6DDDEB45_C5AA0EEF_1E303162_9633147F_18995058_EA3DF84F,
    256'hB03FC49C_A39F7EBC_0B8D0660_B7B988EE_544200B8_64ECC073_75930210_116B377D,
    256'hF03B9283_34DBBBE9_1B0A5A4A_C9049D1D_D2A24EAF_65F369B4_BF89BAE8_8C80C19A
  };

  // Compile-time random permutation for URND permutation in MAI.
  parameter otbn_pkg::mai_urnd_perm_t RndCnstOtbnMaiUrndPerm = {
    173'h1843_60242D1E_3112AA22_EC0148B3_30B2C980_42C12CAD,
    256'h454F3C8C_5BC302AB_6A0AD5A9_C64DEB8B_FABA400A_90D56F8F_43C5E5A3_58B14B82,
    256'h2D63AD2E_669602A4_5B60833A_AD60563D_E0D4323B_393CB122_B9B2D9B5_653459FF,
    256'h63705EE1_8071580D_62D8673C_252F9A6B_B0AF2728_AB2EE7F4_12D84E7E_0E036286,
    256'hA34B5E01_52611755_ECC89849_535E17A1_AD75FB20_7E98CA28_4F818B51_6BBAD4AD,
    256'hB80E4B4D_D5411648_4BB8A227_B0FA4D21_C41032A2_DF0C9AD5_A5BF1C61_8903CCF8,
    256'hED103A4C_7AAD1F47_C9A012DC_ED721908_435683A9_E75C7920_6B249384_29D01414,
    256'h03D7F7A0_32717A26_1E1CA9C5_3823181C_431C5D11_F822E151_011FA350_1749E85D,
    256'h6D8A7A43_9D844609_89DD6400_875D9810_375DC8E2_33A2DB1C_A151B06C_26448B90,
    256'h254C17EC_56BAFC34_0DDA5397_DD426A6E_80BBD097_84AB9954_D920CEAA_E3D7B276,
    256'h253635B1_D12BB49A_92FC3F4D_C6DC6C4B_02605306_92A348C3_27F35173_431D4ED3,
    256'hE6330BC5_1538B080_52F11331_CC3581B6_C1D06A08_82F28F1A_2DD99296_81A06679,
    256'h4A26C226_E745F240_8E0B3E85_E5021642_9534852F_CB54F7D8_C0F9EF02_0C1B6DE4,
    256'hE1D881B8_48A0A39A_73270DD5_46E711A4_9D2B7460_A8BD42AA_4FE592F4_CACE1B09
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hE0CA6281_0904C353_7781FDA7_A9FD8140
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h4CAF580F_3E1148DC
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_dpe_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h11C84B02_31C46928
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_dpe_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'hCFC3B93E_D9E9A3BD_C9B8DD11_5036606D,
    256'h7AD5945C_BA7EF075_31A19300_A2221FEE_30604771_9028FFB1_CD927902_E65AA87D
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_dpe_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'h549A7F8B_247C603E_B168E52D_B007DABD_4D82CD2E
  };

  // Compile-time random bits for revision seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h8D5002D8_B4A57DE8_953A5900_E784BC5A_881E08E5_D542C8CB_0BA1A866_A15FD957
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h1E73CF30_3D7D2616_ABFB15B6_7F128001_14B0DF0C_5890806E_8FB9F7BD_8520A769
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'h518431F6_AEFFF7A3_F1E6A046_32EC8618_FFF5D2DA_BC22016B_66763C58_BD44B7DA
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h92F44E09_254D2FD6_C881E9F3_BA2C828D_47DD8D2A_90271669_7C676A93_8F094DEB
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'hBA0F87B3_253DB0AF_A3B9DDC7_CBEAA357_BBEB60DE_61780386_2E9D9C8A_0BD1C43C
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'hC0B583A4_C35A0898_4BFF9BC6_CE12C239_4BAF1702_E9F57101_282D4A2A_30911433
  };

  // Compile-time random bits for generation seed when hmac destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeHmacSeed = {
    256'hADD44390_72F6189C_6A680EA5_3A88E234_D4F6C4B0_159916D8_35B3EAF2_E929E5DF
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_dpe_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'h0C06DE2B_26C3276D_4CB771E4_C1DF3A41_4CB94254_0B342216_914E680B_8786CD85
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h1E52033D_60FFC069_AF2D6A1E_68EB898B,
    256'h76E7B590_E6EA81F9_588E6FDC_9CDBA357_161862DD_1AE1A094_F472346F_8C2BA6A4
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h39500953_396F6171_82D84EEE_DD6D954E,
    256'h033A0FD0_F499E5E4_9416167A_66B5DF79_8329006E_1BCBDFF4_9D828FCD_87D964A3
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h4E59881F_532222FE_97333ED7_849C1538
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h69B34184_53B8AC09_4713168F_BA548A70
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h64DEE642_C665FF1C
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'hB275AABB_0B574613_086626E5_DFD28712,
    256'h380B56BF_32729182_D3303AE2_87DE158B_E64C1D5A_E71DBE4B_F0CD77B5_0E4243C9
  };

  ////////////////////////////////////////////
  // sram_ctrl_sec
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlSecSramKey = {
    128'h00CFF986_8D1CE165_6FD5D448_9600E3D3
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlSecSramNonce = {
    128'h6F51D1F4_E8B38F7B_EB6C59CF_41E51AB3
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlSecLfsrSeed = {
    64'hC1B2BEA6_8F8E31F4
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlSecLfsrPerm = {
    128'hD588EC22_814A07BF_1ADA59D1_0AA8697D,
    256'hBB507AEC_BA25950C_9AFE472E_4DC61125_4D030CC3_AFFFB1D3_88A05D63_DDF5339C
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h95D9FA55_4B4B9BB7
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h7ABC9398_C51C5551_96287FD8_FBF03D20
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hA517B5FC
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h685C5AAA_78826DB5_BEF1C806_8D77C7FF_04491994
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKey = {
    128'h126C2FC9_1F00E735_11F184BB_ED51CA9A
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonce = {
    64'h30BC625D_517319F9
  };

  ////////////////////////////////////////////
  // sram_ctrl_meta
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMetaSramKey = {
    128'h64628426_DB657DE6_6ADB18F7_836050EE
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMetaSramNonce = {
    128'h5798E973_F633EEBE_88429984_E922979E
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMetaLfsrSeed = {
    64'h682F72D5_5F53F54C
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMetaLfsrPerm = {
    128'h548346E4_9A57EA1F_71411B47_30481D07,
    256'hF16A93E9_C2F163EF_28B02362_C65C4F0D_037BBDB2_DDBAD4E2_E4B3A268_8E6B595F
  };

endpackage : top_earlgrey_rnd_cnst_pkg
