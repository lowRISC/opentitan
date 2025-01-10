// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson \
//                -o hw/top_darjeeling/ \
//                --rnd_cnst_seed \
//                1017106219537032642877583828875051302543807092889754935647094601236425074047


package top_darjeeling_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // otp_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter otp_ctrl_top_specific_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'h54_3A0130B3
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h0576_43886004_60C7159A_11CF2964_8D91B4DE_41120E0A_31677E52_E050969D
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'hBE84F303_80655EE2_6D62DEE6_AE95AAFB_7A44E26D_F9CBEDBC_3D512527_FE67E8B2
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'hE07D5551_0F7DF200_E9385195_DE4F2FB2
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h08A71E82_207A34AB_D439B462_F7FDB8FC
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h20E2960F_A1C63758_8C08C383_74903B58
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hBC3484DF_9B0E9C2F_06F0694C_EDAB6BE2
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h563D7C0C_31CB754A_523EAFE9_0D67C2C5
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h5F3D8CE4_0AF0ADBB_E93A5F9B_AB97F2A9_139A0FFA_956AEADB_13BAAA10_D2336E39,
    256'h9E5F1AEB_58C2A1BA_65D13A0F_E39B01C9_5A626001_CC969493_D06CDB45_0C26A87F,
    256'h7BF58DDA_1149EFDC_5F023299_DFB44D70_A9F90685_9E02C051_85213FCF_029CB3E6,
    256'h2CE6FDDC_BA7F6C9D_2519EA1A_ACC8E192_2AF7B82D_7479CD41_D20282EB_0D61AA54
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hCC696D54
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h2E8C1E35_32551D3F_32FF7F62_75C336DE_060412A2
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h224F25DA_B6226BF5_45B7FC56_675745FE
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'hEC587DCB_2A925376_9D73F614_F297C5F7
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'h024F5AD9
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'hD1EF5544_82059A9C_7F7C28FC_87519D5C_B2684C2F
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hBEE8C0A3_F22571AC
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h967DD7A7_A90EDA29_8C67E0D0_E05D0907,
    256'h9B9F013D_42C2A6B1_80446F21_877B6E17_0F49EFED_F0754637_2ACAB23A_33F4B594
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h62A78D67_CCC2D1BB_CC2B6049_53A9A011,
    256'hF916757D_77469C5C_A3F0D0C2_3B1AE7E2_E5F67E3B_AED1D3C8_E3C5BA11_A2488540
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h812B74CC,
    256'h981F89B9_B95175A8_F02EA42F_7883754A_0EAA875B_D05EE93E_58E0E429_86CC76AC
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h3E319D0B_58181078_00733C3B_12749486_79110A7A_892C5E9A_60398527_87045C5F,
    256'h018C0D16_4942214F_72335B38_5D829509_255A7522_7C8E5937_07083A1D_973D8126,
    256'h8A1B6220_76998424_301E0C23_962F9B03_7F19454C_9E513291_4E356D4D_71772D4B,
    256'h474A8D69_4363366A_667E6F9C_46569050_531F2A83_54801A1C_9F931561_13689892,
    256'h3F677006_287B2940_2B574402_41052E65_52640E0F_5588176B_7D6E8B6C_8F483414
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h534D7AC4,
    256'hBD0CA8B0_3546A981_88556C8C_BF9B24D1_D32C9BD8_6DFED26F_1FE72FFB_B4B9762D
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h3F69D7B0_444F62FB,
    256'h85E1BBCC_E9A23D25_29FC2CA6_57AA713B_124DA452_1A14C7D2_97617534_41488B05,
    256'h85D2C74C_7F2C23C8_CC1179EC_9B714548_9BB894F5_C7A124A9_73566537_DC7C3CDD,
    256'hBB06B6B1_C3847142_16DF2AFD_F0211C39_B9824695_C3E8D792_1A37A8B7_87506C10,
    256'hF8399465_BD559956_913590C4_C3100C18_9C5A7A38_E4AA87E2_D56DA015_AA9037AD,
    256'h08B54D84_7EC2041C_3E73A368_02CB6B6C_D7B4450C_14C312C8_34AF80A9_66150CFA,
    256'hB0B20341_97A16E92_6E8835A5_8B53F751_203CAFAA_DC852C69_30088D78_0FB86CD3,
    256'h096EB4BD_0C8A232A_408304CE_187C0753_ADA40A9C_6012D4CE_3B174A81_6ACF1182,
    256'h17DA2080_9A60F579_559442ED_962FD8CB_971659CA_7C25CBA9_ABC548C6_4DE76106,
    256'h39AE68C0_E46E0156_AA35A923_C084A23E_90962714_3A076097_F5F1A203_2231ABB6,
    256'hC800984B_92C1A0CC_A0BC6A53_F8EB45E4_31601536_D710D475_78D87816_A1B5AE7B,
    256'h0C599846_251D34C2_2DF3B1D2_5971B971_9B1A2159_1ADE77DC_7BBA844E_0A576A77,
    256'h44914C04_E24169E8_BA9257D8_B2B0DD86_A555E2A8_142C2306_F2A6E86A_5149C680,
    256'hA0D13BC7_2403A57E_910978D0_BA98AC03_01408059_305B19A0_976400F0_71070332,
    256'h7E222F02_B8DFC740_E42A634C_509A5C78_19702B38_632B4F19_E53C8440_16FDAA43,
    256'h89C13E0A_238A9AAC_9308E593_E5D017EC_4279FF31_E789B5E2_1B6B05DE_8AC0C0B0,
    256'h9E52812B_E4663137_0E0146D7_4981BAA6_4C6E4B68_2ECCBDA7_46D13905_E87BFCA4,
    256'h5C83BBCD_884C1D19_80871B02_E2AA7F22_61087B10_AF5A11BD_B5906663_6918205B,
    256'h22757A9B_C9555237_724CB356_7C026729_470E9C1F_4C603C28_557898CD_5C26C0BC,
    256'h297F1952_CD6BC344_063DF9BB_5CC6E028_3D2D5B1A_D044C0CA_589F9CD8_D7642B86,
    256'h135822EA_A890F7A6_98ABC478_58D007CE_FAB93EA8_3000419D_B8E4F5A0_6983D436,
    256'h7A5BAD5F_E19A29B7_70C80CDE_C1A5E91D_C85D2F51_846475C1_28E1153F_D037996C,
    256'hA694B03D_CD63A24A_2D9984D8_1AB4571A_8B9646F4_3096466A_BA940569_29A22468,
    256'hF9A6588C_01C5FC9B_26223359_F846C7B6_0E6B5EEE_06606B41_25F5770F_12472288,
    256'hC88302DA_CCBE61A3_F6487D8A_A4D9D4BD_B292789C_821705E3_F1F3871C_0362D19F,
    256'h46747523_44076B51_1E67DB3B_64E830E2_C39D4824_0AF53EB8_4E81E7AD_EE325B09,
    256'hA9BE52A8_9BF1500D_873495C1_C1CC510D_611289AA_C4ED7752_142CE31C_5CA3B855,
    256'hB4C53492_99C5E19A_0C742D23_AA54ABA8_D97616D2_96911010_2401AEC6_DE644CB0,
    256'hAA15582F_0D962621_352567D4_E5BEDDCB_8A4E0FC7_A6F5BA79_67A791EF_838A36B9,
    256'hDE950009_5D4173E3_52296032_97D6A0B8_12267AC9_D6459FAB_F84C3DD2_B628F675,
    256'h508B9AE9_B912E435_A4683151_DD51BF56_3BDD1F40_6BBB157C_1E71181C_EAB625D6,
    256'hB19C8ADB_16F1B610_9C69EF14_53422258_99249C2B_E5AFA042_C14A0665_15BA4460
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'hB7480D9D,
    256'h5001B775_5DE3EF26_18E28371_DD02B1DB_04469E57_70D10B00_69E332BE_0F35A726,
    256'hB339D953_A1DD95A3_F78E1438_9414ADC1_9300E093_4269B3A3_0B61EA4D_9790DE0F,
    256'hB09D2792_D26BF956_5775A284_3FFB7D42_993C0A1C_3D4D2937_F997A3B5_1AAFEBC6
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h2A89790D_B63EFF5A_927C7D96_C2F0B23B,
    256'hA17CAD7E_DE662023_B24CCCE2_E804A4B6_89B48510_F749A719_C4C1DDD3_D5851C4D
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'h4569B54E_4CC3468B_A78749A7_093FE9EB_381742E6_95130A4F_B5238EBB_74B4F311
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h8274EA0B_356B0515_35EAC4E0_98EA131F
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h95C233E6_70A4321B
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'hAD599D4D_F689612A
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'h961D0532_D78D8ACE_1FF82767_391F0F51,
    256'h5416EBF4_A96B95FB_20BC2E1C_472064AF_75C406EF_AD88D3DF_3903076C_A8266A86
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'h95CA1A67_1B6B87F5_F2CFD226_A0445E21_BB53C12C
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h46794CFC_A2B0C6CB_FB61F1BD_7ED0A8F9_26DA506E_D059049D_C9A6E2C1_826AA5BF
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'hDF596FB9_A391C672_2B8B5CAD_051F3EDB_286E5540_01528F8E_9A5E55EB_B82A171C
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'hF1E411AD_FE91411B_1D8EE016_1ECD6990_02EF8026_E474E857_39EF0277_414266B4
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'hF811EBD0_1E7EA4AC_F08B65A5_CF51AE52_8473DD46_61D013FB_44105783_0DD1B830
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'hBF365BBF_C1DEB892_1D7A6896_FD1E6013_622D6614_2EE83239_BA8E92C6_1DE956A5
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h2768B6D5_F1650F1B_01969710_A957DBFB_2E2443F4_FE2D0A76_0F83C131_3D3EF78F
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'hEA4D3D48_54921724_8330D048_F78E497E_63710E97_20AC0F46_C68E74CA_B245BE89
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h11081C18_0F034806_61762D84_BFB80313,
    256'h0EA592F6_3F968D16_D49748CB_C79F398E_21395417_31F82F0E_5E0F2EA9_61C615FC
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h96398950_EDED5E99_9CBB1667_0229D5A2,
    256'h4DF595BE_24C50547_533E86EF_45DC765B_C3FC1C44_92B8CD26_4903BA93_E2074570
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h4FC7F5A2_63F7641C_180B43FF_715AA5A2
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hBD793053_46EBE883_E11EEA60_C36419A2
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'h27F0CBB5
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h8E38B367_E30F41AB_4C553C0A_E96E8A62_1B74BC9E
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'h7C5F7FB3_9AFB3660_BABA1F1B_AC202D76
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'hE627CBB3_0AD1BC1E_181DB312_B8D5A947
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    32'h9C07C534
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    160'h0EEBF897_27773140_0C88D2ED_0175EC6D_E69578D2
  };

  ////////////////////////////////////////////
  // rom_ctrl0
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl0ScrNonce = {
    64'hFA5BA5CF_4337A897
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl0ScrKey = {
    128'h7E31C7B9_4C2BCF03_781EE0D8_B1BA84CB
  };

  ////////////////////////////////////////////
  // rom_ctrl1
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl1ScrNonce = {
    64'hB565E8F2_F8BE62FE
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl1ScrKey = {
    128'h9D2D4204_B2F54BE8_75AE4802_77680CBA
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h442BAA3A
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h959DE8F2_0436D6D5_31FFC06F_D48EA0D0_A8839679
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hA690C16D_D41B3D1F_A05F7ECC_83245CCC
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h8577DAAF_B97C26A7
  };

endpackage : top_darjeeling_rnd_cnst_pkg
