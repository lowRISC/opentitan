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
    40'h7A_29B920B7
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h08A8_477C0620_4249C615_C65B9834_CD591315_52388E25_E74168B1_085D23E5
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h51BF1196_B12E5259_BDED9026_1100C8CC_C2B1BE45_99775614_975D3D2B_32E933D8
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey0 = {
    128'h008E023B_1E052DAC_1E0FCEBE_AC537EDC
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey1 = {
    128'h7848DA13_345040C2_95FCBD76_684E7170
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey2 = {
    128'h57AF0328_8E6C3C38_3A73E698_950BFAB6
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst0 = {
    128'hEA1EA059_DC5C584C_99E3E946_397824F3
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst1 = {
    128'hC0A5A56F_968FD7E9_8071EF1B_FF0C99F0
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst2 = {
    128'hC02ABD64_5FC814BC_BC1CFCFF_9F3E4CD4
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst3 = {
    128'h2214D762_08E9943A_43242540_D2120889
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV0 = {
    64'h9ACF416A_D5455D1D
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV1 = {
    64'h74E7B5C1_5957663A
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV2 = {
    64'h7A827E95_A7385B32
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV3 = {
    64'hFE6728D0_D0879EC6
  };

  // OTP invalid partition default for buffered partitions
  parameter logic [16383:0] RndCnstOtpCtrlPartInvDefault = {
    704'({
      320'h67BAA00A00025E7FC9BD14102DC30C29978A4C70C8DA26CB202F5F59A412A3392B9403C190120BB3,
      384'h6619E1BBA8167005EE5B59B17EF420135EB6A7B2688A16B1C05693E7E037958183C9545358D14AAED1FCF0E1EDCB0316
    }),
    704'({
      64'h6FD5443C2CB8B75A,
      256'h85CE6F2736649780ACF49BFADF4C4CEF4A487A070E2D41C244CB7240CEE69DF7,
      256'h628838F651B4B5E1188FD88EB8AEB542CC2B9D5A79CA02E338758DD6DE796804,
      128'hFBC75FA47FD1EE356B0EE77C01530CB2
    }),
    704'({
      64'h495CA878EB297504,
      128'h66316FA6C7A2CFE54B57B94CCDB5B701,
      256'h5E895532DB9EF56A3F39ACCE8428CD2F10A9BD8A9D3ADE48339BAB0E6739719D,
      256'hFC60FDA3EC7167EDF9CE31192D35CFE634069D6201333F656283E5A7BD289D1E
    }),
    320'({
      64'h8A8E59E8CC6315D2,
      128'hAD9874386DBD4C92E0F24A7DB2A9D1F7,
      128'hAF22D4755CDDD7CB28EF0FF7219351C5
    }),
    128'({
      64'h2CB21F6ABCDC9A60,
      40'h0, // unallocated space
      8'h69,
      8'h69,
      8'h69
    }),
    576'({
      64'h12107E5F93709238,
      256'hA302E95EC6D2AADEA8B6A9D4477ECD98A528E88DD62172CAFE980B4C39261457,
      256'hE17E956C21B003D0BCB1CBCD1EB02317A6BC237A3081D9BCDD43BA90DE4CF7E1
    }),
    320'({
      64'h44E91725013B44B5,
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
      64'h171184A5B1C2CBB2,
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
    5696'({
      64'hA1832965B9E9EB47,
      96'h0, // unallocated space
      1024'h0,
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
    2944'({
      64'hE7DAA2EA63EA3209,
      96'h0, // unallocated space
      256'h0,
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
      1248'h0
    }),
    512'({
      64'h18A937E66A6DF253,
      448'h0
    })
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h8E2E1CF6_5460F23F_B780499E_6FCCE64C
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hEAFD282C_0E33FD2C_07986C2A_511755F0
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h72EE7A8E_2FC45E11_1DF07FA0_67F64056
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hD9BF30D4_8543BEC2_E9A075D7_D536D6F8
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'h2505255E_A0645554_DD5F9355_F5A89085
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hA95A12AB_13E0EC9C_CD04512F_5C01D895_8EF421D2_2BB77013_624B5A4B_FF0BDD4D,
    256'hD6B30B71_7AA80FF7_77A15787_8A468D23_EECBD09D_E6B8F9FA_EAF1A70E_57E8EDA0,
    256'h3A353B76_A2F83350_9ACC7B3A_A3FA7DAC_233E2B78_2306AF30_6A1F3616_5EE14A00,
    256'hEE9FF938_2AF33B47_9718558E_67597646_45AAD1FB_21C18124_635E3D50_A88F6808
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h045627AC
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hE5EA97AA_68690EC0_F6D0D2C5_92C4D895_3E0DBBC3
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h478C14DB_070A6129_BB2945B8_8DC6CFCF
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'h2AE02F47_010CB666_A5E22D33_20F89CAA
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    64'h47E5CED5_D29CC9CD
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    128'hF9E548A4_CEC7E41D_7C5D8489_1A02AC34,
    256'hE1519A2F_6311F642_96BC9BBC_0FCBDAAD_1C9E443A_8770F159_4E284F0C_EE3DD6AD
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'hCE1CF9E2_02920739_6945C95C_9B54BAE6
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'hAEF30D85_77834CCC_6CAAA63A_8E660433
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_top_specific_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'h8151B9A2_3C08F9EE_D04CA1EB_B0BDD305_FFB6C481_8054E0E0_EDB0ACD0_B040FC62,
    256'h9EA7F8B1_7FA88FEE_02E3F086_4223A2E2_3A8CC31E_2DE5E578_D43D2DCE_49E360CF
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_top_specific_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'hB594ACDD
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_top_specific_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h6041F31D_621E6D3B_CB54C6E0_8E115179_6BD4B5DE
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hECB11CE3_B87AAA7A
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hF9B3702F_842EC6A2_A527F8D7_1CCEB402,
    256'h78B2B5A5_391594D2_043B085A_662BD44D_9C768F5F_A4F47757_3EDE3BC8_060A486F
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h7A2601D3_7A75920C_161B1510_4B3FE795,
    256'h73CBEFE2_B63594C8_7680C7B6_EE5B7D10_3825C3B2_F45B2BF0_46AA3230_BA566BE1
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'h819D1518,
    256'h690E6473_CDB24793_91635057_CA1045B9_E1917E1F_F0189B04_A4F7FBA9_60FE098A
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h7648238F_2A754D9F_8A9A718D_53092518_6E6B7B58_57981C72_59687826_807D013B,
    256'h38464590_84076C2E_0B86883D_7A940665_3F515F3A_820C7083_9173205D_39672D22,
    256'h3749606D_305A4A61_03211029_1E813562_4E277F16_85400097_8B871232_15791152,
    256'h1D638C33_5E3C9242_242B6A02_505B9655_2C4C7413_2F9D1F9B_0A34997E_64283144,
    256'h9C1A0405_93770F41_476F3E5C_43087C19_8914668E_569E540D_4B360E95_1B17694F
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h042A75EC,
    256'hC25D4E22_67E3BFF2_6E003AAC_BF7D513A_EA01E9EE_420D5B52_3F6B00C8_1BDED728
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'hC3C6781E_219715AB,
    256'h852397D5_20F0E8B6_31018CF2_820B961C_9770864A_931806B0_360D2CA9_A57AE133,
    256'h50545A20_2849A868_9E1457D7_FBB4FB8B_48D2CD4A_69228229_A17C1A34_657590A6,
    256'h7315DC92_24F12EC7_8599692F_061C59E7_BED59E70_0B329BC5_71E711CE_0D12B126,
    256'h6A6E2E7B_D2BE422B_4801A68F_C9E3CE80_AEC4A446_603D499A_371B9608_B7941B98,
    256'hDEE01E4A_4005603B_1D3B0B76_0A318347_3ACF08BE_46D6DC65_66CE57FC_875523A2,
    256'h91D61566_E1D1DB65_DCDB116C_B51E8A89_C7261EC9_C9C18564_7B5AA8BE_93ABA1F3,
    256'h075100DC_A9501FEB_82B2B746_154D13BF_5B91320C_7C8C1462_9A5BA616_746CAC12,
    256'h93DA5259_4164C870_A0D6D480_2D0C2ADA_71D2B01E_6ADD02A8_4795DE22_B388C8D0,
    256'h5D959738_142A165E_34363752_C326EE1C_A064C2AE_996A0EFA_4D8C8F1B_0448681E,
    256'h80C6F232_4294E34A_6FAF2EB9_F571456D_A3359F06_496A9425_34CB2989_6A222CDA,
    256'h753C0542_78E0832B_116B4AC9_87D1B3FC_6E86D059_D0BF570D_0411BD69_51C53711,
    256'h0CCF950A_E63911F4_E0B1A1DE_A1FF126F_E9F7782F_1F5B53A9_E9321F84_1AB19662,
    256'hE9346614_6BF4BDD4_424BE8A6_75BFE4E9_A44F2755_64F4DAAB_1F572F05_4D43D5F4,
    256'hC6A54141_D8AF2F58_B96E82C3_53943824_510A0729_D7868CFB_2C8E31E6_DA242C80,
    256'hD3111925_3C6AA540_B8A6278B_F006BD40_4898915F_81E55567_BFA91C25_1ABC86A7,
    256'h4EEF8F55_BC305436_0A2365E0_55DA03E0_4E63DC3B_44F79DD8_D2052226_93E82E33,
    256'h15F1C641_2E1CA5E6_B05A8055_93708038_A2B08928_64CFE082_117F040B_4CA7924C,
    256'h94D9AF9F_0895D084_9026B591_7B5D9842_D4A3C293_B7AE4516_C137C43F_7602B624,
    256'hAE589216_56DF351A_E107074A_812344DD_77492272_97287191_F9DA1161_3B213017,
    256'hE96828D7_721CFA42_7E78444B_6563046A_BA3EFBB0_A513B97A_0C5378A8_3E33A352,
    256'hB5073871_4BC51D60_2DE76401_788A6218_0D060217_9ECFB5D4_65C87885_D171F143,
    256'h216843F5_A23305C6_4A02646E_E9400884_1BA91903_6619AA9D_7C5AE306_ADBE355D,
    256'h5B284737_E9E58134_6D0F4546_B67B61E1_A4ED42E8_A36C7774_2AE9ECC2_6DA412D2,
    256'hDB724367_7F1A9501_C008C000_15EAE94F_4B5C5810_605E30E3_0ED083AB_D32E6813,
    256'h5ADB1636_A1625865_819FF178_EC09C0AF_6672656A_4BA8262F_8E6DC7EC_100E96F7,
    256'h471F3115_8B945E3A_4CA5A46F_35A6C120_52990425_A0E06CA2_45310C38_DF65268E,
    256'h0E1277E5_C603C9B1_4C82975F_4BA5CC58_6A35211E_9E89F10E_E2861AAB_B0A84509,
    256'h50285039_C26C12F3_B0CB6ABD_0F6202E8_F947AD5F_DC06F89C_4BB0D62C_1AD24A81,
    256'h942AA1D2_3E44A52A_91D40B88_E5396AC1_90D3F6C6_B95C1C08_3DA7C2E5_5A32922C,
    256'h0FC9CD01_57403818_589D894C_4D99188F_03EA7099_83B24CBC_A2C3963B_1607DF70,
    256'hA6F7B91F_A62985BA_8A5880E6_B8D86BC1_796CC230_5CDE848E_B7907B01_566B1890
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'hA9AACA4D,
    256'hB84A32E5_C6985A1A_6435118B_5F5F3FD3_B9313116_B67192D8_56DD742D_40E072E4,
    256'h17AD9A5F_261204CB_CC69A214_7819B290_A4BB0264_347C0F91_B0CEC93C_0129D85B,
    256'h95801DBE_03F17E69_DC260A79_998EFF5C_710B6783_8ADFB99A_5ECA6716_72CF19BC
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'hE4D3967C_CC7D4325_616A64EF_7A88AE09,
    256'h7ED1D4AC_CB3D2040_D1BDFE1A_074723CA_85D99278_8EC50396_4FD87271_2DEB0AE9
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'h9A07EFFE_E457DEE8_2B6E0666_3C291739_FF0E7D64_4758FEE1_C58564CF_346D9622
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hE5371091_366EFBD6_1B0CB470_B944EF80
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h6E573B44_B643EBF0
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'hC5DE019F_C073C4C5
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h6C3C15DB_9AE58526_58A4859D_FFAB075D,
    256'h306ADE3C_F569F020_E2D172BA_F9C610B7_B4A0F38A_08C24DFB_1EFD7104_64F22526
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h74C7FE91_8685399B_1C3E88A5_8055A5D2_EE97ED0A
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'hADCDFC5C_5F76D4A8_E259D88D_FE9B670A_A0DD992B_FE5D2E12_489D2250_4AA7AC1C
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h67F59CBA_5482C1E3_5E6E3335_C20CC778_FC309917_B9C870AB_E0895D76_F862EF81
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'hF419E3C6_CDC8662C_71EAC141_666E443C_6492D9BC_F7A82420_750E5DFC_5E3ED4F2
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'h907532E1_79EBEC7E_D7D3A5EF_4982F73E_D91C4B1C_D0C85EC5_E548B401_84A69EB1
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'hE5439646_0E36C55C_459EFE9E_43836FE8_78E46433_7EBCAE32_38DCDF7D_E88B56B4
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h05E02BBF_D73849C5_11F7F0B7_9F91DCD1_D589B4CA_C4372C38_5F89D902_019DABB6
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'hDD57022C_77EDE860_9C409D90_5B3C7819_B26A6743_28819928_C5D79BF1_DB63D11E
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h1C31BBC9_A8C73FC4_CC3D14CA_6BC0B968_12DE7C77_5A54FF19_343CB320_40B34907
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'h68889D27_E0BA8588_D34C05BC_F127DAE5_8B65D6A2_51088099_B37107B1_CCCF1A95
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'h5F03DE1A_8447BF83_B69C50E1_49CF5178_4A9D7AC6_91306E5C_56CE38CD_7D7E3B1A
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'hBFB79781_89A21AE8_56F1D908_E3F70DE3_43D2226E_9E864465_A8EE55EC_0E6A2967
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h89DED5C0_AF59EE62_F1FD1BBE_BEAC2205,
    256'hB1FA5E94_E72EB7EB_1A713AD1_5D2565D9_AB4FBCD2_E17C406F_48D1401F_8A6A5228
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h6F6954C2_7A9AEFBE_0BC9EE44_0C514CCA,
    256'hCB019995_F31FA958_859293C5_591AE604_A92A3037_60EB8D77_85A7BBDC_E1D6A02B
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h6F0F24F5_DB8EF02F_9FB0A402_3D8F96A4
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h1F062BB6_6B228701_E8317CD4_BF08BD66
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'h84A1D596_CC57E137
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h876E1071_92350A20_CA4CEC97_5A519551,
    256'h2F01EFAF_8916C9AD_9F38E9E7_DAEAC708_1B6842D1_60F75F37_F91EDF4B_C0B87328
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'hBEF1F0B9_24C470AC
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h5A998099_85DC415B_A1EACED3_82D54C9E
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h378D030E
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h0D55033F_A315DB64_4A782476_5CF3E958_0FE63B54
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hA4D3D738_71FDAF5A_D0C1DD1E_95F99D71
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h29CA6861_A4425B9C
  };

endpackage : top_earlgrey_rnd_cnst_pkg
