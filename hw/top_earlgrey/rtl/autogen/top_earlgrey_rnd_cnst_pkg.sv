// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson \
//                -o hw/top_earlgrey/ \
//                --rnd_cnst_seed \
//                1017106219537032642877583828875051302543807092889754935647094601236425074047


package top_earlgrey_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // otp_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter otp_ctrl_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'h23_D532C0AB
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h35F9_E2744982_8087A351_B19228F0_5A157307_54E0D985_07166090_139642D1
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h55D70063_277642B5_309A1639_90B966CD_494444C3_BCDF8087_B7FACD65_E9654CD8
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h5BC66D10_208C4FB5_1B97BBF4_D12C378C
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hCFD6A5A5_BF3032DB_51FA1EB9_2F6CE10E
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h90F9C5C0_6F733DC9_11A321DD_4C0AC240
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h6D467215_DAB3F2B5_4A52E672_8678AF07
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h18068E34_4D2EAE4D_73C8FA54_DE8AA4A4
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hF258F3B2_A145FD19_50AE55D6_93E57968_117E66DC_634155E0_F8150242_862EB20E,
    256'hEA9A1F75_44716551_512A112D_ED678CE8_24A08E29_C772795A_358EC30F_1BEDD1AF,
    256'h0EC9D9A9_CF36A2B1_30D32AFE_121AF734_F628363A_AA0E93D4_5C423690_ED05BD1E,
    256'h710F22D1_095889FB_D8A7B57F_B1E11DF3_67C1C1ED_E3F35CFC_8F6E72AB_DD73A9EE
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hFBF8B708
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hD07AF5EC_56811520_45096BB1_32D19ECF_EA7E1AE3
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h42692B08_9A6F99B1_A7AC0842_24ADE461
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'h2980D48E_6C6493A5_0EEDBAC6_A46B7A8A
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'h9B2C7AEC
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'h791B870B_95B872C3_00AAA2FB_686C7FD1_E284CFD2
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h11E64066_908ADFD5_918F8C56_3C92184F
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h1C76A61E_112578BF_9F469FC4_82FA14A8
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'hF2B75C26_5C9CB3B2_F1C44A72_87AB4C06_18822E92_A084A048_FFE9FB86_140A79D3,
    256'h8055B24B_5F3B3EA7_9BD7F203_D55EABF9_F733D9B0_CC2CA2B3_94F2526E_4430C2AF
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'hB4F5B43B
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'hDA8C1FC4_8584ABA1_E2CB43D2_DCD1C7E5_FBE98182
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hEC27F13E_B602172C
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h352B301E_82238B40_C93BBF82_AD9C4B5F,
    256'hD798CAA9_06F1D455_52D9E17F_F105E60D_CF5B86D0_73398AA7_66BA075B_AF300953
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h347B55E5_DFA46903_140E8241_DB2FC0F6,
    256'h7BCB7A38_520972B0_1383C5D6_B3A5D16B_A07C69B3_C6CDDB66_262AA512_1C4FBF3A
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h80499E6F,
    256'hCCE64CEA_FD282C0E_33FD2C07_986C2A51_1755F072_EE7A8E2F_C45E111D_F07FA067
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h5227992E_22693A16_3F8B5D8D_58914A1E_3283106A_866C4C2D_760E4978_31847C29,
    256'h67377924_0A710D95_81424147_06663948_8702639F_7A144F17_8009209D_0834447B,
    256'h7D612C33_2A0C6F5B_901C007F_890B1B0F_35180357_3C151F6D_9E3E6082_774D2819,
    256'h8A74941A_1D73729A_53884E68_65114623_459B8F50_3B07923D_387E596B_266E9796,
    256'h8E4B628C_702B2101_5C2F5104_13125A9C_935F5455_645E9805_25367543_85305640
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'hB666A5E2,
    256'h2D3320F8_9CAA47E5_CED5D29C_C9CDB468_773EBACE_C14DA34C_505AEDC7_0EA184C7
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h31814580_84094D29,
    256'h114AAF9E_6620F99A_DEC77C9B_A71AC27A_C3B24C36_9A2380EE_E7AD8789_9D20E92F,
    256'h178BA48C_C15C4AD2_88EE8389_C0C94D23_069974B6_781CA794_7D5580D1_56EF1F26,
    256'h87C2918B_C2BB2852_789C6C2A_B686D75A_79D9A0CD_C32DD448_A504159B_466ED4AC,
    256'hED492AC3_430B878B_B97D2D65_4F75D289_7309911D_D65A319B_345F9DCE_184636BA,
    256'h4889E16F_4B19734C_388B5906_D0C25F0F_F1C88DBC_D5C09F09_A8E90A87_1E06312C,
    256'h0D451FC1_1AA10DA1_5F4BC6C1_9FF06800_801923D2_CCA0770E_7B9ECE10_00AB1844,
    256'h55451678_BF2466F1_E609995C_90B4C542_4AEC7C2A_6C17E054_9F8C4570_497A7F23,
    256'h20CDE16B_D5812D31_081779B4_95A6AC71_A2E2C044_95384E7D_9064394B_808500FD,
    256'h5E944E99_0416C628_F2619A16_5B67B515_A66FF91A_A6659B93_5DD19CEA_F9E9432C,
    256'h4ABAFC09_B22E0681_781B27D6_A64B9D31_3078BD9D_62C401BA_5021D19E_07C30836,
    256'hA1AA46AE_B49E643B_1613C672_C5406C3E_3E3CF00C_6AD42E6B_19788B0F_8A1B0192,
    256'h1F8D1198_2E3260C3_217BC09D_58DCDDA5_C81332D9_6F0BE2D5_18631D09_1C6A8E62,
    256'h88A57D62_5CB268DA_4A1251EA_CB999E73_DA7B0D07_6216131B_6176FE58_5AD6C36D,
    256'h204EAAB5_8CE44DD3_3908EF3C_9C203801_180002BD_D829E403_8A594083_06051018,
    256'h5F99E539_7C59DA1D_34BE8D67_A11B64DA_B73CC062_EEA47404_95AECBF2_E1A2ED15,
    256'h92609270_84130447_1118D408_6016A074_B73A0488_52382B0E_00BEA459_C6558A08,
    256'h0DC6B4D8_246EEF87_34B41C1F_DA111229_88668C71_3EDC751E_CF862E63_8EADA39A,
    256'h11368A10_6DD6725B_B72D34AA_BA8960AA_08A4806B_7B91C513_E963610C_356BD5A6,
    256'h10B7E702_284AC5C2_8C1C1360_80F70ED2_8BAB9985_5721CC45_D9D38711_F28DADA0,
    256'h4FE7201C_0C5DBAD6_438F05DC_368C6964_C7B9B224_950884CA_2A88F1D4_0B4FDB15,
    256'hC31669E2_22C0FC40_55D8D293_1609489D_99188F03_EAB2970B_C0E58E8A_81F7DC29,
    256'h7EAF0B58_A5880E66_19796CE7_CBD8DE84_AD07907B_A56F5240_6F94CFDC_7108AE2F,
    256'hEB8D9FC6_DD7C3821_25B1DACE_7EA956EB_78DF7EDF_5869420D_5488E929_B32BB82C,
    256'h034F0463_1D44815B_E4299424_C1942D4C_351AE4EC_B2A80022_A20FC531_122680A6,
    256'h1265989D_5FCF814D_B56346E0_41F20F50_7B610FBE_6A789263_BF55A544_36366541,
    256'h713E0998_39B1F845_9419151E_645A4152_F4938058_FE4D87F1_08AED752_5DE7A530,
    256'h57DB799D_DD1D1CE8_EDF344C0_7C145A11_6A933C22_56EF20EC_1B6E1A2A_197395C5,
    256'hB610B8AC_29498A9B_10A5A0F0_82616E5B_A2BC711D_A92ADA45_15918DEF_3AE040B2,
    256'h16B55EAB_118F6F4C_DA766E4B_9FE95692_485547FE_B44F5C19_48F478C7_88CC8E86,
    256'h6A2B169F_62903B09_5381ADB0_5EF74C82_3A214633_9983AAAA_83615549_7245CE59,
    256'h207353CF_51326915_81A9D80C_594A99A8_7725C437_02304D6A_EBED385B_67193E8D
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'hAC290425,
    256'h63AE4733_313AD269_6788A873_5B27982F_5007A24A_125F876C_9CA6DDEB_52AC92F5,
    256'h600D2A41_BC465EFE_57AA3B59_BD6B0A40_21636342_0F041ED2_9A965B68_FAEA3E59,
    256'hD4F2E2A0_B42EB9A8_C3AB227B_50766D2E_AEC89EB1_3B07E9BF_4EE42784_136D42C8
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h73A93266_A6B6E1FB_1DCE0B54_C02F3E00,
    256'h63EB8BD5_858F5418_A040791C_3C694CD4_8C9CA20B_DE5EEF7A_6BA157FD_0939B457
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'hA8F072E7_7EE4859B_243F92CE_B098BE6E_65C35948_0858C396_11E658C9_7FB8D3E9
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hCC0E7F8F_A8725200_C726C8F9_0EF5E2B7
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h4BEEE27C_FA19EA57
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h6CA8A822_5C8E1705
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'hB931FB3B_12EFADCD_AA1008BC_15948906,
    256'h6F5D9C83_21E10C03_E5E61B0A_893E95FD_0654DDFF_CACE97A5_4CD668A8_358ED44F
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'hB87FDDE5_8A44756A_1C05F720_93384394_C8D7AF15
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h20BDAF59_FE2AE209_B8325D2C_8C35FC96_0679B106_A87E59E6_AEB1B530_2D334010
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h70251696_FBB4BA16_9A6CD82F_AD46A0A5_C04009BB_934C7EF7_B83B6E40_610B4309
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'hFCB9DC54_D4276137_F9901D09_A76AEAA1_9DE5C579_FD38BDF3_8F0C21D6_A52226B6
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'hA4A7BDB0_5FE92161_5BF2FF98_4540F7D4_3ECE76B4_EB133637_74ED2ED4_5545E927
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'hF6D9E4AB_AC398D42_C745EEF6_46C1464D_CA86DAFD_7C7C71E6_058DDFD8_71C51CAC
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'hBAF4410F_06DCC036_FCD16FCD_E97D1718_91105DD8_95E3A1D0_A19A16D6_DBD8B20F
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'hC9E662E1_E1B4982B_3E8EFF63_890DBEAE_926FD468_A77EFDE3_DE5B4CAF_4776A247
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'hBABA4C99_08ED16BC_5415EC16_D28C5355_1312FCED_CF2832A6_6CEACF8E_D4D5B616
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'h177DD43B_56FA754E_1F53AD65_8193B563_D9BDC6D2_AEE84852_F0CC7371_ED3A6FAA
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'h516C144B_34C96DFA_BB6F6E79_208A74F3_5C79F397_C4E4C7E2_2B758184_8A90A125
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h4B2276BE_C9FC1A7A_5722A9AA_CA4DB84A_32E5C698_5A1A6435_118B5F5F_3FD3B931
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h3116B671_92D856DD_742D40E0_72E417AD,
    256'h9A5F2612_04CBCC69_A2147819_B290A4BB_0264347C_0F91B0CE_C93C0129_D85B9580
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h1DBE03F1_7E69DC26_0A79998E_FF5C710B,
    256'h67838ADF_B99A5ECA_671672CF_19BCA6AD_C1EBFAB6_11F19E72_62E0A491_970E51B2
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h8E7026D0_E5DCE9E2_65A416A8_12231CFA
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h76E3D982_F8FDCEC9_AE1AF0B8_CD9E1760
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'h6EC98106
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h85097395_A09DABEE_6DDD67D1_948B1A89_9435BE41
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'hFEE457DE_E82B6E06
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h663C2917_39FF0E7D_644758FE_E1C58564
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hCF346D96
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hAE357A7A_3B2CD206_3D7F3AB3_043AC11B_7B211B84
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hC652D737_2432FCC4_D3092BD6_383FDBA3
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h5279FCBC_D2BD2C13
  };

endpackage : top_earlgrey_rnd_cnst_pkg
