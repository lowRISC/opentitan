// Copyright lowRISC contributors.
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
  parameter otp_ctrl_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'hE5_492495FB
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h6482_62947457_01858A3C_69C17603_5290E995_71F6A131_311B2C27_A3143510
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h9B54CB12_1F7002A4_05ECDCF1_FEB0FA7A_14877EC8_863787AF_272EFAA5_1F0DE710
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'hC891D47F_F7209F95_D614848E_38361CD9
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestDevRma = {
    128'hB7EB23D5_32C0AB44_E1E92CCF_EBADAD91
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h93A3EE4E_CD8C0324_62B3E185_49CB1E70
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hD5A83DE6_673D2C1C_0A7B5517_6264E55C_329C8AE4_725AEAF6_72815012_7AC755D7,
    256'h00632776_42B5309A_163990B9_66CD4944_44C3BCDF_8087B7FA_CD65E965_4CD85BC6,
    256'h6D10208C_4FB51B97_BBF4D12C_378CCFD6_A5A5BF30_32DB51FA_1EB92F6C_E10E90F9,
    256'hC5C06F73_3DC911A3_21DD4C0A_C2406D46_7215DAB3_F2B54A52_E6728678_AF071806
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h8E344D2E
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h9F9B7FE8_40E948C8_1C267CB6_3462CBE5_22ACB935
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h9A1F7544_71655151_2A112DED_678CE824
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'hA08E29C7_72795A35_8EC30F1B_EDD1AF0E
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'hC9D9A9CF
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'h533AF241_D5CB7D38_813842E4_13DF7C18_8BAFDA86
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h7FB1E11D_F367C1C1
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hBECEBF0D_EF50254A_65C6739D_119595AD,
    256'h38858487_CCCCA011_4B006481_AD8698BA_18D32D4F_36E1C2B7_EE77A9C6_E35FCE3B
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hA85CFF02_6C68F563_E5341B21_8890EDBB,
    256'h5BD96B6E_8C7DCAC8_C144F92B_EDC47586_C2569C97_1F48101B_CE0E8D14_A793B78B
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    160'h265C9CB3_B2F1C44A_7287AB4C_0618822E_92A084A0
  };

  // Permutation applied to the concatenated LFSRs of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h7E067351_8C7A7545_59718364_876D217B_99242307_2F7F2A57_4137956F_0D788A9E,
    256'h1B198188_11321C6C_9F656804_2B923C42_0F252D98_2E49538D_0C546A39_175C7408,
    256'h00101246_1A318E28_89829A3F_664C099C_7C85761E_91603620_389D4D15_90353461,
    256'h025D9718_694A268B_0B9B5B1F_13299327_220E405A_4750564E_8401621D_8F707758,
    256'h437D4F6B_3D723A05_63946716_9630446E_522C335E_033E3B5F_4B558079_0A148648
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for LFSR default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'hC8CCC2B1,
    256'hBE459977_5614975D_3D2B32E9_33D88E2E_1CF65460_F23FB780_499E6FCC_E64CEAFD,
    256'h282C0E33_FD2C0798_6C2A5117_55F072EE_7A8E2FC4_5E111DF0_7FA067F6_4056D9BF,
    256'h30D48543_BEC2E9A0_75D7D536_D6F82505_255EA064_5554DD5F_9355F5A8_9085A95A
  };

  // Compile-time random permutation for LFSR output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h3D28047E_70A54FF0,
    256'h743C7C92_17057967_1C96D518_291C2315_82610011_088D81D7_8BC4DF56_DD6492D8,
    256'h58056B8E_CE536350_C1044408_842512BD_EDC59493_9997795D_2A875537_32AEBF1E,
    256'h42709136_6C161A8A_7E6670D0_46A40244_BF1D39E1_46166531_D575FA2D_6E2A862E,
    256'hECC39B72_3A822F82_325EC9C4_6FA32DE0_91058638_DC729011_6EDDA793_0A6CCA78,
    256'hA408CEB7_3193E9D0_B9AD9661_506A1F99_B435CB44_6F41C942_BCA175B9_3B1D5557,
    256'h86BF4BA5_11562B05_6AA7DCDA_45F17B0C_866BD760_617D51A1_21D8F20B_DE770E3D,
    256'h838821E1_FA3DEC03_53023A64_D75655B3_1DB13539_9BAC4C30_8AC592B0_3EBA8D8B,
    256'h8144483F_0BA664FE_73857C65_B33BD38B_A1AA2F09_B2AAEF07_E7563135_822B4719,
    256'h91242468_6C0EC6C2_205EE538_1A668929_1907989D_AE1B4160_0AC26C13_239AB594,
    256'h89A9F045_068A392A_F54EAE91_010C745E_919A508B_AE74B6E6_9781B7FE_5964A2C7,
    256'h12D568F1_F2EEED4F_DAB094D5_A8DFD527_1C35E539_59626FC2_80F541A5_2D23427D,
    256'h62870261_0E124998_E16C88E8_DB6D7A93_30754ADA_2A16A9A2_6C869B9C_500642A7,
    256'h92C7091D_E782C24B_7EEBDA06_D3AFA2F9_C59334D8_84DC92AC_1D25625D_2D54E771,
    256'h4529DFC7_62D933D4_B322CB02_0C483E37_30151819_905F231A_E6888004_B8AA490A,
    256'h8443E20D_59C74466_7E1F2544_4D3C3B93_47BCB60E_9475D2CD_284E5204_2B8A0530,
    256'h14EC7A0D_D10D409D_E76A98D2_60313A4E_1C1767F0_9CE2B145_C498E453_1ED0CD1E,
    256'hAAC3E6ED_1578D4A2_BCC18623_25CAD497_E83B8187_6D04EA85_A987CFBA_442C8902,
    256'h14088003_42E1A6CF_AC8BF91C_7A255BD4_3CD17D1A_7B788B3F_419A11F8_752968EA,
    256'h0248C038_547B099C_8BE0DB82_AE18644C_30D1B80E_FD5BC5FB_FCB3BAAD_11795CA3,
    256'h907415D7_7C114C56_9763EE22_75226F1B_6BBACA3C_E1096964_90E63250_3B7B8717,
    256'hCDC55521_14809628_1AC52035_01CEB7D4_00225752_A500C071_819EA065_D9558C84,
    256'hC20591F4_CE1AE8C7_68609620_B1693D74_E22BEEAD_20D9F214_F187A21A_B06C6524,
    256'h2A959E79_A1357413_BF8BDBC2_5B50E9D9_8414AED1_D3E57319_452AC6B8_4B0381B9,
    256'hA4C4012A_247F9144_1C36F393_A640E461_6586856A_629CA9FB_D90B5857_1C7AD07C,
    256'h437386B3_30A9273E_6ABE700C_3E69A69E_B1BEC883_0E3B7C0C_28A3E2D2_D7079D05,
    256'hA18111F0_6A17053D_9E508062_9207327D_25565508_9A7B905B_18591A23_E25C0DBA,
    256'hB598349E_A42DCEAC_290802E3_F7FA7A80_6873C205_04239A61_B24CF120_DA6D696E,
    256'hB02AE4B1_9039826F_A9CDE53D_AD71E20B_1C500103_16F80993_CB25B5CD_41A865AD,
    256'h314D8FA6_8673AA4C_C6683247_0A529829_8C209A66_AF775983_257F2B23_C3581C77,
    256'hC6327811_682A23D5_8D8131A4_59D96755_69730B2A_D285ECD8_6A2BCC10_AD231F6A,
    256'h3DEC9ACC_DA2CED3A_15FA7234_8A55E778_3F7A82D5_A589700A_E21E3B5C_14413C4A
  };

  // Compile-time random permutation for forwarding LFSR state
  parameter kmac_pkg::lfsr_fwd_perm_t RndCnstKmacLfsrFwdPerm = {
    160'h61E179D4_B88DB29F_68C4405D_4E8F6D92_DFC103EA
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h1A6C2B38_CE96A742_D4D5C3C2_6435EEDC,
    256'hDE606154_85F5D6EA_A3127312_DDBF7FBB_3E0641D3_46786323_888ABC0F_326A541E
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'hE24BE7E1_C96737B7_26A4C6F0_4993B3E6_AAE70F22_AAF748B5_7C320264_E157E2C7
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h4A280332_61EE6CEC_10075C55_A820F842
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'hD43EE1AB_1B3D78F9
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h92D22346_9898EB2A
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'hBA87C33D_D8319DE0_A103ECEC_EAD96923,
    256'h98EFC95D_9B938350_5FC4B550_B9B459CA_A265A3B0_311F5824_12AB4C5E_C71371BF
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'hBCE26820_3CC807B4_B242F394_F262A5B5_35F3F5AB
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h5E456F3B_26D15F55_84BB9879_BD249785_2C23D0FA_289C3348_CE364ED5_34970E1F
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'hD45EC606_BE134FC0_8318BD29_B22B08DF_647BDC30_068E7513_200FA828_BFEE3ECC
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'hF02417FA_68D00453_4267F60B_34A8F072_E77EE485_9B243F92_CEB098BE_6E65C359
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'h480858C3_9611E658_C97FB8D3_E9CC0E7F_8FA87252_00C726C8_F90EF5E2_B74BEEE2
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h7CFA19EA_576CA8A8_225C8E17_053E44B6_8DD7822A_6859F2CF_52A55FD1_81B082D0
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h3C583756_F11AA5B3_7F9544C4_AA90EB97_E1C0F808_6F627A28_1C5681D6_566641EE
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'hCCCC8887_6AD113C5_0AD1BE4D_94DCE8FC_A54128A3_860AE1D3_493FBEF6_B9BA5DFE
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h4463A461_5EF46762_A794A8C2_597E69FB_259B9619_14CD75BB_FD36BA48_E780D27C
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'hD582540C_7A68FF25_4EDFD852_829FECCC_ABD4AF9C_9032DA20_BDAF59FE_2AE209B8
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'h325D2C8C_35FC9606_79B106A8_7E59E6AE_B1B5302D_33401070_251696FB_B4BA169A
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h6CD82FAD_46A0A5C0_4009BB93_4C7EF7B8_3B6E4061_0B4309FC_B9DC54D4_276137F9
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h901D09A7_6AEAA19D_E5C579FD_38BDF38F,
    256'h0C21D6A5_2226B6A4_A7BDB05F_E921615B_F2FF9845_40F7D43E_CE76B4EB_13363774
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hED2ED455_45E927F6_D9E4ABAC_398D42C7,
    256'h45EEF646_C1464DCA_86DAFD7C_7C71E605_8DDFD871_C51CACBA_F4410F06_DCC036FC
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hD16FCDE9_7D171891_105DD895_E3A1D0A1
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h9A16D6DB_D8B20FC9_E662E1E1_B4982B3E
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'h8EFF6389
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h20CF1518_026733E2_DA13FF70_E4256FA6_F4D956E1
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'hEACF8ED4_D5B61617_7DD43B56_FA754E1F
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'h53AD6581_93B563D9_BDC6D2AE_E84852F0
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    32'hCC7371ED
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    160'h1C018097_939229AE_B33F5BA2_47DAFB32_45E555A7
  };

  ////////////////////////////////////////////
  // rom_ctrl0
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl0ScrNonce = {
    64'hBEC9FC1A_7A5722A9
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl0ScrKey = {
    128'hAACA4DB8_4A32E5C6_985A1A64_35118B5F
  };

  ////////////////////////////////////////////
  // rom_ctrl1
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl1ScrNonce = {
    64'h5F3FD3B9_313116B6
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl1ScrKey = {
    128'h7192D856_DD742D40_E072E417_AD9A5F26
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h1204CBCC
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h22E6EAAB_1B8C3284_97FDD1C3_C33017F4_AC378A8D
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hFF5C710B_67838ADF_B99A5ECA_671672CF
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h19BCA6AD_C1EBFAB6
  };

endpackage : top_darjeeling_rnd_cnst_pkg
