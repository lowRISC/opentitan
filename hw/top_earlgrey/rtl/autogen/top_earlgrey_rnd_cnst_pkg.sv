// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson \
//                -o hw/top_earlgrey/ \
//                --rnd_cnst_seed 4881560218908238235


package top_earlgrey_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // otp_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter otp_ctrl_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'hCB_0157A3AC
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h3946_DF803226_3D64E474_A1A11054_1E61A557_70D0A331_10222592_C19479D2
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h605FEFE9_977B00B6_FDC21D57_7A172D04_7DCF0EEB_BDD268AF_D4E2506D_F1D0603F
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h9CD62F17_8ADC74D5_3D8AD0B6_00E7A1DD
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestDevRma = {
    128'h2F1A43C0_3DD4FF9B_887AB752_1CA6CBD8
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hD7107BAB_98B07574_3F7AEBA8_1E1C4EC8
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hEBDEEE29_11062E03_9F8C7E1A_FA78A1D4_2886CC89_AE759CF8_65B22A5F_28DE2ECA,
    256'h36AFC2E8_A402302C_BDCF2B48_19AFAA0A_11CB6837_1EEF174D_98315696_C49A8EF5,
    256'h3C96F11E_4F43FFD4_21E456B4_D6A9D1D2_AB4A836F_1545EBF5_0FF87BC3_FE8473A3,
    256'hB8A698EB_44C3B582_1FC5BAE3_E1BD5972_3B69B2D7_B5330424_C30845EB_1F7A5EEF
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h762A1F91
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h375ED89D_2A1D3286_2F7A7785_F940950C_C1CBDB05
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h3925A2B2_B291A984_70716274_C976B810
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'h6DD974CC_66D7F9C8_518EEFB7_5AC6B952
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'h8242CE57
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'h9EB0A8F5_24A38F50_A1658338_21DF3607_BEF3365B
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h4B9E2FC1_918D324C_4CFB1A95_698EA1EB
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h7868F849_707838F5_47A2C2A6_4A91A9D7
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'h03429D8D_73DEDB65_D2B0751B_90255CCD_E50A2C9A_B31CAFB7_5C007285_A0AE495E,
    256'h2F5F51FD_2ACF2129_01174C95_76A112CE_A79B5228_2399833D_A888C025_46E72EB6
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'hF09A26A1
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h8D51F377_9EA63579_4CE550B2_476E096B_C165846C
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h690709F0_9E8597D2
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h18C91866_7BFD0701_C2E7C825_AD6C5429,
    256'h18C8E8BB_AA737B5F_CFB7A8A6_CD054048_BF9B54A1_4CFF8E69_DC8DE000_F65C955B
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hF8633CFD_E5AFA6B5_07549420_EAED688C,
    256'h110A9306_B63992EA_71787DC9_F634CC30_916F7B48_4A6E3195_D37BB278_8F153E40
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    160'hEBDB78AA_E822F2F4_44DF087B_34854B57_FA1B481B
  };

  // Permutation applied to the concatenated LFSRs of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h35211013_03181580_8909584F_6726255D_0417556D_9E2A2273_41642E82_6136760C,
    256'h4E9B0616_931F514C_8D0B793D_66428130_37878800_20024950_2B68999D_0A6F864D,
    256'h4A94193F_54293A1A_63774685_2833577D_1C323974_9C0F2C05_31834027_1E705E1B,
    256'h758E453E_7B52906A_8C8A9848_5B11122F_622D083B_569A9153_781D9223_8F6E385F,
    256'h47957F96_4B847E24_7A726065_97597C3C_075A4371_6C0E5C69_340D8B44_6B14019F
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for LFSR default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h48F16180,
    256'h90982699_8ACE3628_C0CF0E58_B7088571_8609FA79_565DCBA5_40ADED8C_8D5560AF,
    256'h97340EA9_29AAE07C_399BB65D_74BD1FF1_6F281690_2BBE7ED5_4814F745_1C011AFB,
    256'hB712B66E_42C19103_58162E3F_B2368EBD_E95C97FA_3B0E8F66_29A16E94_D4E43991
  };

  // Compile-time random permutation for LFSR output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'hC116F8EC_1BB4A423,
    256'h18778492_5ADD5D7F_1736506F_13C55AB6_AB1A7075_10497A2A_30AAF41D_15E7B06A,
    256'h0605324A_931E4CA2_06B335F1_26DC4205_9684F991_522E8483_09936099_5DB9A761,
    256'h86A6CB55_A44A6637_901577FC_4838501B_71F8534B_27EC9C6B_CF3C31AE_BCA3A810,
    256'h266D6010_89E99C92_C7CC3EBD_711A5036_8D938C71_D234E9E5_644C636E_E1AE0B88,
    256'hCE78281D_70E775FC_1EB389EB_C09F7C1D_1AD4052B_89680D14_11EE2B68_C35E576B,
    256'h91112650_C8FE9C0E_5371C1B1_6E89371E_5B48E601_7A5460A5_833A78AF_684C4E02,
    256'h9C1D62FA_5A2C4C98_468F60C2_09967AA8_276072C0_90C3B20F_1BAC1804_4271BC55,
    256'hA5CA5265_DDF621B0_6B5613D0_ACC0EE00_90A6904D_29992B4C_87F7D1D9_359DEB94,
    256'h8AB24825_91DAB12E_A3B060A1_4F1B144A_43DE23A1_7587C94B_B0118C6F_F38A6360,
    256'h5C998B17_1151D0CA_38BDC3C3_E1C0184C_F029215B_1A78E4A2_5014B29E_3042E567,
    256'h9EBB4D62_B791C625_E5F4787B_4B68A4D2_D0866A29_ADA8AC86_D280510C_D399D229,
    256'h7148CBAC_A4C39BD3_7C136EC3_56E1171B_8B7460FA_8800950E_886C8F79_D43A5B6F,
    256'hA9758987_9F779682_ABA5EC58_FD5C4D5A_FA47B36C_1AB24FB0_ED461EE3_13949320,
    256'hA8572862_24082384_6B223D9F_50263D66_411455E1_FE6FDEF8_74801A26_82100C5D,
    256'h1F92FCCC_3A8E56DA_4A2F6DD3_C22D052C_286D9214_8A11F66A_A345732D_530FD9C0,
    256'h0E3C3E69_6B9DCD43_44033698_A6E877F4_B3556330_06CC1726_49BDEDC7_4EBA68C1,
    256'h236D33C9_1531C9D0_E221820D_9219DDC0_A45781A0_A9E15A7C_AD53DC81_42FB8413,
    256'h00D1A693_269C3DCB_46A51AC4_070B2923_987A6122_45AA5CAF_DCC89AF3_4F53C666,
    256'h4B068DDB_5A2E054B_B26E8E0F_59F47D0E_B7C31762_A11C5937_E82FADAB_A4A98B41,
    256'h82D37190_AD21A858_2383E7C7_C6172E81_F9EE6E21_64675464_9547336E_35619128,
    256'hD0AA1DAA_4A418549_C5A3D9E1_7DAFE195_22459691_12227A93_679A0006_5DC9B103,
    256'hBF4EF30A_4E6FA1CB_854C7ADD_0A552FB9_8954E9DB_6CD96BBE_B9B1F081_E00D5954,
    256'hA1756301_05F5ED3B_7D71E085_09685F24_9300A00D_09B6D94B_946C695B_B5706C06,
    256'hA866273B_B55F134D_19FCB953_99B46EBC_1D53F240_8B09417A_E0665515_04203018,
    256'hDA29406C_02E5919E_0EB185BC_41D789D9_E3A57C8C_B1410E89_21D29C54_E0244E4C,
    256'h611C0DE8_16AE9798_6AFC6459_A2C5681D_B48357E7_38B02F1D_3104AF12_D58415A4,
    256'h712D138C_FE70570B_3E0C8F96_E2D41049_89A0BA28_AA5A55F4_7C0A47E2_21AC2AE2,
    256'h544D6281_48FB29E3_C2D6B59C_02819412_E1EE5DC7_2545193F_EA567542_369473B4,
    256'hD8638274_A22F162D_B6A8C0AA_8B48B249_9230A188_DEBA5607_3DBC94D0_0B61C266,
    256'h8B63F0A9_9E454000_2B750F58_4E8368E6_7B5C064C_C98A3131_3B8D4A46_A628EFC6,
    256'h3214C371_F7282854_AF8B797A_41CC5629_95038A5C_14128AA7_E03EF942_AF63ECC4
  };

  // Compile-time random permutation for forwarding LFSR state
  parameter kmac_pkg::lfsr_fwd_perm_t RndCnstKmacLfsrFwdPerm = {
    160'h6C52BADA_026047A3_4F972E09_20768872_9FBCF8FF
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'hE16CB1A4_455785BD_0DC24673_FD21EADF,
    256'hE99C19F0_E0090DAF_78E94915_8B4C20F8_EE8944FB_00A9FA45_D07D2F5A_3CB2B6B9
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'h173B0217_51142EB3_0B9482BD_8E7D31D3_E1A2619D_66EF6CB9_16FD6C86_4A510AED
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h83D2D2E2_4871C35E_3AEABAE7_7182CDEF
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'hF9F77516_F1177315
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h733AFFA7_32F4C491
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h2C629940_F4ED827C_37884C63_AA6A4E74,
    256'h55EC93C2_1BB87712_ED5D4CA1_E274C8DD_B953F0FE_03A46F59_8AC1E1A0_9FCFD865
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h5216C347_ED2DE7AA_0BD0C6EB_D905EEB7_3203A483
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h414C190A_D0A09D14_4FFC0C0F_EA081CEF_945B641F_096B9F3E_9A494BA3_5FCFEF0D
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'hFB223E8A_B704F249_EE3FA822_276C45E5_88ED40CF_52C8FAE2_D054A711_49771822
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h2EC37360_E23D4DDA_559ADABC_F099937F_EBBF048F_AC328BA1_BDEE0CAC_A987BE4A
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'h4ABF486B_16740B20_BC32B13F_F07A13FF_21CE605E_0AC01985_8F73D707_CD0EC1D3
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h3DAAEF20_E285FA65_8FDD1B42_6C037151_B16C8D44_4C444F39_6F4479CB_795CF94B
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h9E409D18_381BD5D5_6821E298_5E479971_05C4900F_25557467_5985B210_E1A968E4
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'h5E5B35E4_60FDAF1F_F382AB01_95E33689_D99BCEBF_2B79B683_9264EDF4_DE2B39F3
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h94059891_A38BD1D1_6C763BBD_90347E58_152D7FCA_99380365_25AAA3F8_9E3DE8F1
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'h278645E1_1D7CAC76_310205E1_9CD3F2ED_294A279F_3C6D0649_A905CC9B_10A67A16
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'h161FED72_416DFD29_3DE3A18A_8837B0DD_4CB694DD_540451D7_69D28E1D_9E76007B
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h7A9E0F6E_3D591A7F_D8C7BA26_4AF78F28_AEE0D28E_4D638D95_D1806E87_0336CD96
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h1D2049F3_32011CAB_7D512B69_B6B766DC,
    256'h84760801_C9AAE19E_8A6DD42F_94A9A15F_A77F118B_21BA52C5_D59D755F_58D2D862
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h44D2DC25_8CA12CC7_0B776B16_DD95013B,
    256'h9569BD77_059093ED_3CE77AEA_86FFD82C_B1CDEE3F_CD6039C7_C0402496_5B7C1E1C
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h07548A9B_F5956E74_82848DE7_D401512A
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h2573043A_8E0AD9B1_56D761AD_532F38F0
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'h767AFF4B
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h6CD8E170_15D40914_D8A70990_BFF77996_28F1F957
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h755CF00B_D7432C3F
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h8CD4E7EF_F1B9EC59_CE812447_C5714595
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hF17463DB
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h7D3352C5_76E13E90_EFC895C1_36094776_203E9B4D
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hC10D8DD7_F82D1584_4E53A6AF_23823858
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h2F4520C3_2D5E0D6D
  };

endpackage : top_earlgrey_rnd_cnst_pkg
