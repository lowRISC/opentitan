// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson \
//                -o hw/top_darjeeling/ \
//                --rnd_cnst_seed 4881560218908238235


package top_darjeeling_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // otp_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter otp_ctrl_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'h57_7A172D04
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h7271_845D3422_30948D28_15608597_48985900_59E1E53A_34422CF6_1B51A0DF
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'hEBDEEE29_11062E03_9F8C7E1A_FA78A1D4_2886CC89_AE759CF8_65B22A5F_28DE2ECA
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h36AFC2E8_A402302C_BDCF2B48_19AFAA0A
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestDevRma = {
    128'h11CB6837_1EEF174D_98315696_C49A8EF5
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h3C96F11E_4F43FFD4_21E456B4_D6A9D1D2
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hAB4A836F_1545EBF5_0FF87BC3_FE8473A3_B8A698EB_44C3B582_1FC5BAE3_E1BD5972,
    256'h3B69B2D7_B5330424_C30845EB_1F7A5EEF_762A1F91_29C2B7FC_BAE1B800_9909ADEC,
    256'h2586C494_F5DAC82C_170B9DE7_9AF5B271_0CE4BFCA_C18ED453_28D7D63C_A958AC39,
    256'hF21ABC39_25A2B2B2_91A98470_716274C9_76B8106D_D974CC66_D7F9C851_8EEFB75A
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hC6B95282
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h8D6FD224_F37074B2_FE0CF087_4B039879_9B2DAB28
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h5ACA0C8D_4B9E2FC1_918D324C_4CFB1A95
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'h698EA1EB_7868F849_707838F5_47A2C2A6
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'h4A91A9D7
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'h81B8F4F7_0D166BA5_78FFA5CA_159243DD_98E8CD00
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h4C9576A1_12CEA79B_52282399_833DA888
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'hC02546E7_2EB6F09A_26A1661A_0D5DB701
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'hDDF4ED7C_6F488781_71C320FD_F1FDEF79_13525470_E04A549E_BDD80D4F_7B729F25,
    256'hA1926E51_73690709_F09E8597_D26DFC56_265ED80D_03E335CB_77683AF6_573E4C84
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'h4A75FF9A
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h01FF2711_770952C3_0E13575F_AC5BD4DD_502E45B9
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h78F79F87_69F9E185
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h65693BFB_3E2F6978_7C187AED_80EDD050,
    256'h9A23326C_98FDE56A_0916F621_295D3799_E23C5D00_0EEC754F_DA4B12CC_1C7FA281
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h51625930_4F83AD02_9361772E_D0FEF98A,
    256'h07F66FF2_E98C1B2D_CC5025F3_255284DB_C2448AB1_D7A19AF5_D3A7C247_87DE6A38
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    160'h7FBFA00E_47BF71DC_7947873B_F1A7B4CB_AD77105A
  };

  // Permutation applied to the concatenated LFSRs of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h1A06086A_775B2B11_374D5A9E_2A1F9B6F_6D4C7E4B_9F316085_2F654A99_4F494272,
    256'h43919555_23105D15_962E2C7D_218F4416_0330530D_529D8E09_26862018_98025013,
    256'h83454080_6C04129A_7A54071D_79943B6E_6235610A_75700C2D_327B9C5C_92177487,
    256'h0E331C88_6B760001_41059338_571B2814_5F71847F_89474856_27193F3E_6682293A,
    256'h34978C51_678D2439_6473581E_590B633D_814E3C8A_36788B7C_460F6968_9022255E
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for LFSR default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h2E3FB236,
    256'h8EBDE95C_97FA3B0E_8F6629A1_6E94D4E4_3991FBDC_31303EE6_BD9C4285_BE6303D3,
    256'hE48A9FAE_8AB504B3_C162C97E_295803BE_F65B6566_6292F222_316E41C5_5EA3B7A5,
    256'hDED4BE1F_548D0A22_72AD3124_BE0E850C_631EBF06_28DBA982_A4523510_FA7D3B97
  };

  // Compile-time random permutation for LFSR output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h3C436606_C45E0123,
    256'hCCC44064_27E45E27_8D34F6B3_3289C9FF_176DD0CA_8A849311_F6C1B508_2981DD83,
    256'hB32038EC_1824AE07_4A404AD5_EC10BAA5_2A1C797F_87656790_61AC96DC_394B962C,
    256'h9A8EAB19_31106EB1_652049DA_D3A5CEC0_6A456B88_5978CF7A_44CAB848_39D5C4F0,
    256'hC3636A85_CAF46BC9_F4746028_D0A1FC8A_4B685154_E865D4D4_781143E4_71A9892B,
    256'h06B484E2_9C230A42_446C93E5_59F32EE5_B43AC2A9_C69776E3_10B05BCA_D6315488,
    256'h80D748D3_4865C397_22932431_97CB2450_CE4DC3C2_6C220765_4C7D326B_52A41ACA,
    256'hAF6F624E_6A725937_1D76BE21_80707498_2E8B1601_C48BE79D_C5666D49_BE392BA2,
    256'h177D82B4_B0895DDE_92D110F8_D212ADC0_2AFF2648_193F0C35_81E08C15_C54F84D6,
    256'hD9620960_C8839A21_131A6DA3_8F461C26_4944787E_C87D0A66_45431149_4482469E,
    256'h082B6A75_718E19D2_BB0E55A1_C0DC7A28_08D30B7D_E7D0EDFD_7FB00828_05059E07,
    256'h3592B7EE_DB79744E_6129DC6F_126EA091_8A2C58F2_8A627C1D_85CEE472_1D91E6DD,
    256'h592D129D_E24B2730_BDA86C6B_C54871BF_8975022D_1EDEDAD5_57BC1598_2E89A55A,
    256'h91B4A014_43357692_8AE55974_8CC50A4C_4E7C37C1_37543569_D171B938_2DD183EA,
    256'h3C02568A_9AB83DE0_F0E9449C_69C7FD95_8EA33892_A0B356C9_EF1C3F5C_03556F58,
    256'h6649EA4E_B2DE559A_E26EE4DC_0C4E8594_9AB0A889_971BE889_0208EC5B_199CAFC4,
    256'h0B07641B_64114587_8DD7BDBD_0F4805E4_68A18840_31DA07CB_F330EA39_636744BD,
    256'hBF4F0928_14B861B6_FC527C4A_11F68884_23732E14_85DCB00E_8F62CF97_E9EC7F10,
    256'hD100CDAD_EBABB263_670B3556_38006EB1_72BFA0A8_D0B6F73A_EB93048D_BCCF2454,
    256'hC7274388_F6233648_667EB0A6_A6682696_8C6BE2B5_4F6E5F81_431BA653_0809A69A,
    256'h6875E9FB_46A6EB40_070B2223_9A088564_15AB10B0_1D673243_15D800D1_BA0AAE78,
    256'hD6651E9A_0C0AC196_910B1A93_6E053B54_4654D845_D43F13D0_B322A41C_CDB94986,
    256'h44A512A8_76B0ECF6_15278685_A3D9E17D_AAD19522_45969112_3F7A9367_9A00065D,
    256'hCA2903C7_4EF8B8C2_9ADBE873_01531EB7_42B44BF0_62553A76_DB365B0F_C2AE6C60,
    256'h78035655_285D58C0_417D7B4E_DF53EC21_425A17C9_243BA9E3_42AFBE52_E5180F56,
    256'hEF5630D4_B1D98A47_0D57C4D3_469D2E54_E66D1BB6_C754FC90_9B08B094_17C68665,
    256'h51504203_018DA294_06C02E59_19E0EBB8_5B41DD78_9D9E3A57_C8C80E10_E9F21D29,
    256'h294E0244_E48A91C0_DE816AEB_6A6E61B3_A7E1668B_15A076D2_0D5F9CE2_C0BC74C4,
    256'h12BC4B56_105691C4_BC4E33F9_C15C2EF8_323E5B8B_50412626_82E8A2A9_6957D1F0,
    256'h291F8886_B0AB8951_358A0523_EE978C28_5AD6700A_06504B87_B9771C95_1464FFA9,
    256'h59DB9542_369473B4_D8638274_A22F162F_B6A8C0AA_8B48B249_921CA188_DEC25607,
    256'h3DBC94D0_0B61C266_8B63F0A9_9E454000_2B750F58_4E8368E6_7B5C064C_C98A3131
  };

  // Compile-time random permutation for forwarding LFSR state
  parameter kmac_pkg::lfsr_fwd_perm_t RndCnstKmacLfsrFwdPerm = {
    160'hB2F48B90_7BAF5899_E1CDF3FF_0904B957_007150D1
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h9E6F6DAE_8AB2B076_765490D3_50F10B20,
    256'h688DF0AE_DE4008DB_45660168_27E19643_29DEFE75_C45773FF_AB8E5F07_12E3ED20
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'h2EBA3F71_E4EBAC6F_4F9643C6_2E4091E1_1907A673_4572487F_85F60D1F_1F254A38
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h01CC3DB4_DB727F0D_96DE4A0E_05A5DC7F
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'hF64F231D_7DB9C9BD
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h90CF465B_59731B72
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h02E84BD5_BFF8B63E_9C33CBE0_39FAD42A,
    256'h4F6236A1_15B1D25E_0772325E_94A63F66_B1C195A5_1F9CC3EC_59FED021_93411A18
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h26CA8669_F97286B1_78F86CA6_985B81FD_3A6AC417
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h8F73D707_CD0EC1D3_3DAAEF20_E285FA65_8FDD1B42_6C037151_B16C8D44_4C444F39
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h6F4479CB_795CF94B_9E409D18_381BD5D5_6821E298_5E479971_05C4900F_25557467
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h5985B210_E1A968E4_5E5B35E4_60FDAF1F_F382AB01_95E33689_D99BCEBF_2B79B683
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'h9264EDF4_DE2B39F3_94059891_A38BD1D1_6C763BBD_90347E58_152D7FCA_99380365
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h25AAA3F8_9E3DE8F1_278645E1_1D7CAC76_310205E1_9CD3F2ED_294A279F_3C6D0649
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'hA905CC9B_10A67A16_161FED72_416DFD29_3DE3A18A_8837B0DD_4CB694DD_540451D7
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'h69D28E1D_9E76007B_7A9E0F6E_3D591A7F_D8C7BA26_4AF78F28_AEE0D28E_4D638D95
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'hD1806E87_0336CD96_1D2049F3_32011CAB_7D512B69_B6B766DC_84760801_C9AAE19E
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'h8A6DD42F_94A9A15F_A77F118B_21BA52C5_D59D755F_58D2D862_44D2DC25_8CA12CC7
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'h0B776B16_DD95013B_9569BD77_059093ED_3CE77AEA_86FFD82C_B1CDEE3F_CD6039C7
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'hC0402496_5B7C1E1C_07548A9B_F5956E74_82848DE7_D401512A_2573043A_8E0AD9B1
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h56D761AD_532F38F0_767AFF4B_BB54571D,
    256'h7BA3EBC3_93927B56_CC945C44_B5348892_0A7555F7_7BFC936F_EA411188_8D196ACF
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h43EEF65B_7D755CF0_0BD7432C_3F8CD4E7,
    256'hEFF1B9EC_59CE8124_47C57145_95F17463_DB6FD530_F6331E81_C7753E50_D3CF1164
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h99003D01_80063719_91F8FDF8_344ADD67
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h7AFE9E6A_7BBA1DDD_C10D8DD7_F82D1584
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'h4E53A6AF
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h8BDD7B67_D592A834_9A6C0745_A6879BC7_D0559E04
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'hD7C90B2B_3C3EF8B3_80C4E835_FB113AAD
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'h6D7DCA2F_2C7D9BF2_459D71E7_95890EB1
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    32'h9BA14A52
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    160'hBC44D0E6_ACEF2CE8_7E92F1C1_BC0CC42A_12B569F3
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h9042C8C7_CFF5B4EC
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h681D5A3E_F37CD3F7_FEF64E04_C83E6287
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'hD40D8254
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h14283C14_F1D27AD3_4D7CFBBD_B056EFC8_6CA23248
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hD9A0C8E9_A6805472_C5BAC69C_84128B66
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'hAB7B55E0_3C2C8EA0
  };

endpackage : top_darjeeling_rnd_cnst_pkg
