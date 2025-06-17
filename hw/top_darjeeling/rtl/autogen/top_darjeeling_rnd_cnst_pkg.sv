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
    40'h58_FA9063CE
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h2DD6_809079E6_7935A195_848E7CA5_065C4701_8D980335_588C44F1_494026C8
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'hE34F64CE_978305BF_C3481A21_62EA2792_B7508F1E_AB067AF9_54DDA549_1439A9DD
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'hE6320801_FDCF25A4_FBA52839_9117069E
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'h77C887F5_3DDA6FB4_EF8758B9_9027B6AA
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h7468BC0B_D8D70368_E7CFB11A_99675B14
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h62406193_35A9E2D1_23834D18_744778BE
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h5E63C087_E36838B5_6B1A45F6_FD312F53
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h53FA7B2C_E9FC83DD_AF1DD8C5_A42E2AD2_4FA02221_B6FF5AAD_7A9C09D5_D9FDD1CF,
    256'hCF512835_C0CFAE2E_D0C69FA4_88685CEA_9BC1C89B_FB7399AE_F5C6EB5D_6E4E2341,
    256'h6A0AA6D7_AC7EC9C3_304470FB_E505F964_9400CA98_64FD4CE4_9D2CFC6E_CC102540,
    256'hEAD87347_00A52071_32689471_AA822BC5_1CDD4D37_AC2D246C_4264F37E_C1982017
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h94ADDA1B
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h2C7C7806_D8FE46F6_51C95DC1_B36BA445_54DE4E42
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h21D8CB69_D4F3A15F_AF834CAD_515D76BD
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'h37C7BEC5_F33FDCA1_1A72DC05_A2313B71
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    64'h8E6D6DBB_8EC647D1
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    128'hB7742874_B5231769_5C3CDD61_4D1C1702,
    256'hA7EF13BF_561E078A_9826CCAC_36BC9E9B_99886231_93EFC9E7_254ED330_584BAB38
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h2482CC34_468C37BF
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h57677E4B_32BAAAFA_F9E2C130_99A62759,
    256'hB8BCFDE7_F5D21971_4CE90122_93D9A10B_8D0095F2_8D42D180_31771FD3_2D08673B
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h01C841ED_1BB4E7F8_222EAB3A_08F24AAD,
    256'hB3ADC36F_31D67C97_7E44D069_EBC31053_65638747_A68F8C19_49968D9C_D5DFD212
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h36270315,
    256'hF91066FB_63A6E6EB_54493C06_31CD3062_ADF6D00B_7E756F81_353C10AC_316A9C7A
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h9107678E_8F011852_4A1A5A0E_9F544D2A_5E69054F_53802641_71333A0D_5F0F7E1B,
    256'h57616A39_11970B42_56640230_8C832D6D_9D84776C_121C3B86_4B8B731F_2E595C48,
    256'h452F3D51_407B829B_7C080C94_27873575_5B287865_95898D8A_04936832_1606179C,
    256'h50253F24_317A4E19_235D7F72_92109690_2C3E1E66_36135815_740A1D37_476F2162,
    256'h60467D44_76797085_3899039A_1420986B_49552243_6E004C9E_3C810988_63292B34
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'hFD7F6334,
    256'h613AA93B_656444D7_0350A89E_BC0CFBD0_A03925FC_80535F27_7451D2BE_0C46FDD2
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h62A473F8_E39C84BB,
    256'h85A51AE7_85766453_5593E451_6657F9EC_35BD6326_31EF05D9_7C75C393_841A7879,
    256'h13690B8A_C6BED552_A4726571_4BADC7B1_ED1892FC_96D1C0E1_3443ED20_680D63A3,
    256'h45D83317_A5EC171F_8D63DA2E_DE924DB3_A11FC6C6_74293C83_45955C2B_96A797A6,
    256'h893B2CAB_542781A1_41921326_DCE02F06_49AF9700_B98A5E66_92FE4CCB_F6E41408,
    256'h6E9AEA19_5E2F61D8_57C00759_882F6117_3AA1DE74_44018291_708A407A_0CBB836A,
    256'hA8256DA7_A2416527_D2725246_3420B51E_817F0EE2_B6700FD1_66EA85BF_E081C587,
    256'h901E2841_204E6712_962256C4_9C405B32_8233F135_0627DB94_63B162D8_79E1899D,
    256'h28FA3ABC_A6A6E06D_BAA2348B_0F9205C5_F2B34317_2C2C6E76_D3833A3F_C4E28615,
    256'hA06A954B_73031C0D_AC649399_DFD3E1D5_9FC24064_F4150222_D47B57AC_22CA056C,
    256'h8B7762D6_142F0590_471E9A34_AC84A546_2529ADA7_C8E649CD_2767E1FD_9D79D581,
    256'h56B50C55_2AB5AE53_089948D3_7FEF8333_179A1457_ADCA42D1_D3996655_89E0098D,
    256'h1B2CDB3E_B9A6C865_42423606_6998982A_EDA1BC61_054070DE_CB3EADDB_7D2D60DA,
    256'h23B43C1D_DA92085A_04820B38_FD17E36A_ED06422F_4A6243A4_EA403E99_C25745EE,
    256'h38671369_2E806044_C8961AB9_AA79ACAE_7523144E_E4975EA3_C8F10EB1_573182AF,
    256'h1249F30C_B42B7984_0539046A_8E1F5F50_98443D1A_9CF5C5C8_C20299A4_524B1FA9,
    256'h06A17190_3BC47C5A_5BF8A977_22826ABE_B63CD5A7_10A1580A_26256F4F_D9489E03,
    256'h509AF6A0_B4336AE2_A14E2C23_C461236D_4D44540A_4F48C518_AF5F869B_5095111E,
    256'h552D8611_44313F07_86E8801A_0940283A_11DC35CC_61F81F4D_DCBAC167_7EE753AA,
    256'hEF9B0AA9_CD684960_E1749726_6B26EF0D_0EC32A34_EFAFB019_291297DE_D7E5F6B6,
    256'h065C392E_53D51220_11759B11_D1A1A800_36799322_E0F38941_139620C0_538119A4,
    256'hC42A4A8C_278D5C9B_F115AE00_76590973_1232DF51_F5DF6212_85AAC341_1217CE87,
    256'h9424C3EC_E09DCA63_551974C1_C8840C31_6BF7A316_646ABAA4_E19350D9_B5BDBCE9,
    256'hA004F6AC_45670487_259D7010_A04A41BA_5C1DBA08_357EE0AF_686202B4_B3008A8A,
    256'h02A512F9_BA8254C3_4A98096F_91A4C148_2F91434A_C1862E77_80D9A723_05BA5439,
    256'hCF77BA16_A491E994_DC394FF5_B65662C8_DA2944C7_8A7128CF_21458791_F1848C38,
    256'h5DF0B003_E4425391_091525BC_0028C855_796AE1DB_F5D095E4_F3C1B40E_4D13AE45,
    256'h982D7954_F558CC44_1CC08ADE_C2EA1C26_ADBBB22C_1E0B16B0_104140E3_5AE36626,
    256'h3439C996_6A50B201_3A6D9BDD_3B4EA0A7_D016945B_731EED8C_CB6305FE_69DDD7E2,
    256'hFA600C92_F62037D1_79D0ACB4_F025D70A_4048FA3A_395E9115_B22E8EE7_667DF24C,
    256'h9B312013_2EC42270_812F02EA_B0737691_B4F9F737_5A66C207_65892322_3737B041,
    256'hA0A3AE14_0B11C52E_18F2CD43_0B71840B_1CB259BA_5B1A5857_09628FA7_62F0A2C8
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'h82C54E14,
    256'h81730F66_854723D0_0560945B_6C126FFE_C03BF1A9_85028FAE_5ECA762B_77B0AAA6,
    256'h9486CFF6_100543FA_654B7719_79A70DDE_33FF89CF_0ED4D484_BCBD6B2A_E72E3514,
    256'h5B5F97C0_E9B65E98_CEA48C3D_F219340A_563DA5B6_396FCE53_002A2961_AC84BDDA
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'hC955307F_8181637F_E30D17BC_5FD019B8,
    256'hBD607664_9BD90393_0A125620_7CCCFAF2_AAE4DA6D_6AC9E472_23F1EBB9_68D2B144
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'hA575B899_B4CAAE05_6CF2B853_53E1A339_75E7B120_9B868A4A_CD919ED9_795D5F51
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h9AA8CD47_AC68B656_50A1BB5A_4A6DBF0B
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'hC7C1C7AF_8402BACD
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h250ED896_0C88B4B1
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'hA3FB9AF7_29349F5D_820605B3_62D23A1A,
    256'hC4993DCD_D3E0E35D_E4510AF1_71C08CC5_150E2271_C0BEE942_F6FE966A_D17A1A9F
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'h6F92165B_3355778F_DD0678F9_470BA75C_8B08809A
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'hB6EE6E7A_D485FF3C_A72C2242_223CE6D7_0F17B4F4_B32818AA_49D125B4_DEFB1F3C
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h0BE8A29B_E065C26D_23550BBC_139FF646_1763D7E9_66A8A721_9EB2E8EF_9F11A152
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'hE6C71AA2_3B886441_6E750C01_A3339C6C_7AA11244_ECD28A62_CB1B8510_78C2A5F1
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'h8EEE28D0_B562043B_7312EFAD_871F92E7_527DA865_D661281F_E98DFCD7_2E3C6D15
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'h0A85D630_09596F79_66C5C68C_AEDDE4AB_7C65FB8D_59618284_064D7194_E4707ADA
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h81F8A6DB_14CA845B_EEE60798_289AD4FB_0DF17682_96390152_700E078E_C5A951B6
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'h27CF2CCD_155D84FD_ACED736E_93362C8D_A83C5F4D_D2093E4D_2A70DD99_DCF4CCAC
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h341A2F1A_2704F5E2_1287FA16_8AF251B3,
    256'h70D034CD_A6051526_62F4D11B_3245D594_3EA5FD2E_4BEA016B_7911DEAF_01DF7425
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h47371445_D6E39551_45E3074D_9CA9E8A4,
    256'hEF06A6F1_4A5C8FCA_C0D6396E_606A620A_9FFB2375_6BDA420A_9E7BD1A7_C41E3A37
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hB747D3D7_B758B37D_1D1CA19A_079C48D7
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hD4E67100_A6AAEBE4_5B6F09AE_FB72895E
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'hC90D8763_15DB9AD8
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'hD5813489_3911FA70_A6380E0B_53A19676,
    256'hDFDF5DB4_2966A81A_0C857C16_572C3760_52C077AF_ECADF1F6_1AE88C93_33C8FE6E
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'hC9ADDE7B_FB79FB9C_C4C0B2D1_AED6700A
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'h44EA3E7E_0610A663_D52B082B_9AEF0E42
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    64'h6DF4866F_E88A8BAA
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    128'h31325502_0282C197_B789FB87_992C785A,
    256'h8EA335A9_C81B3474_BDC76B92_1DAA054C_BD103F18_6E542CEC_FB75E691_7E5CBFCE
  };

  ////////////////////////////////////////////
  // rom_ctrl0
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl0ScrNonce = {
    64'h37BEBB1D_8879E257
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl0ScrKey = {
    128'h23B9D533_23886587_4EF2D375_583C209C
  };

  ////////////////////////////////////////////
  // rom_ctrl1
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl1ScrNonce = {
    64'h027D35C5_794F680B
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl1ScrKey = {
    128'h124893C2_2E6A22F5_AD2E7591_ECAD6CCA
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h220DE3C0
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h3D1A8B4F_92EE1C92_C5F55AB7_7F30C2FE_74124060
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hF2546EA8_45A7ADE1_002B84B7_39380023
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'hC25C3DEA_F38D871A
  };

endpackage : top_darjeeling_rnd_cnst_pkg
