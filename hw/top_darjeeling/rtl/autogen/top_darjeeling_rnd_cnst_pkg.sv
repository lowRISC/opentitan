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
    40'h91_93A3EE4E
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h4561_1E994424_5E238D65_F22518B4_DB08A3C1_0C574C82_755A7074_A1609023
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h42B5309A_163990B9_66CD4944_44C3BCDF_8087B7FA_CD65E965_4CD85BC6_6D10208C
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h4FB51B97_BBF4D12C_378CCFD6_A5A5BF30
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestDevRma = {
    128'h32DB51FA_1EB92F6C_E10E90F9_C5C06F73
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h3DC911A3_21DD4C0A_C2406D46_7215DAB3
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hF2B54A52_E6728678_AF071806_8E344D2E_AE4D73C8_FA54DE8A_A4A4F258_F3B2A145,
    256'hFD1950AE_55D693E5_7968117E_66DC6341_55E0F815_0242862E_B20EEA9A_1F754471,
    256'h6551512A_112DED67_8CE824A0_8E29C772_795A358E_C30F1BED_D1AF0EC9_D9A9CF36,
    256'hA2B130D3_2AFE121A_F734F628_363AAA0E_93D45C42_3690ED05_BD1E710F_22D10958
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h89FBD8A7
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h45409290_FEB8A1A9_2BB336C3_47362BCE_183E7DF6
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'hA1DCD048_88055411_66F1EC8C_EB42692B
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'h089A6F99_B1A7AC08_4224ADE4_612980D4
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'h8E6C6493
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'h19940855_6273344F_66DC3A13_2D96717B_7F8BF434
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h6175FC10_F939792B_444E521D_4711E640
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h66908ADF_D5918F8C_563C9218_4F1C76A6
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'h1E112578_BF9F469F_C482FA14_A8F2B75C_265C9CB3_B2F1C44A_7287AB4C_0618822E,
    256'h92A084A0_48FFE9FB_86140A79_D38055B2_4B5F3B3E_A79BD7F2_03D55EAB_F9F733D9
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'hB0CC2CA2
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h8861BA15_EE26B9DC_8D2BF4C0_C11EFFAE_0C86AA56
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hF6037B9D_ACA18EB5
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'hD74F8E8F_D1287D2C_3F0C6222_9F15DE87,
    256'h9CEB6026_7A355C9D_9385B76D_072A98AA_6C681BBB_33697C2C_502D3C95_2F4D11E0
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hF663AFA4_DE80AB21_56D09063_E547750B,
    256'hEA101E7C_F6F38FE1_81F1A46D_98984717_130DA2C4_AF75D23E_5B48B8A7_B032C57B
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    160'h14975D3D_2B32E933_D88E2E1C_F65460F2_3FB78049
  };

  // Permutation applied to the concatenated LFSRs of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h5F396421_34995213_1B3F3544_576B291F_3A142268_031C045A_7C4D8224_7678370B,
    256'h1860203C_985D7316_4F6D6306_5C888641_9A27898A_69580D4B_740C9601_081E0A0F,
    256'h9D3E6587_6A195377_1A8B949F_8C462345_842B7D3B_97913D61_62592680_8D718131,
    256'h79385B15_10474A00_2E939C02_664E7092_092D8342_48549049_7E6E7B95_32508F12,
    256'h05253675_43853056_40677F1D_115E2F8E_7A725517_512A6C07_9B330E2C_284C6F9E
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for LFSR default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h61CCBFAB,
    256'hD3E1FDA6_67E04082_478C14DB_070A6129_BB2945B8_8DC6CFCF_2AE02F47_010CB666,
    256'hA5E22D33_20F89CAA_47E5CED5_D29CC9CD_B468773E_BACEC14D_A34C505A_EDC70EA1,
    256'h84C7A341_93D59C73_5B5B4E2C_BEE5AB93_CB024D6F_8C0C7001_10CBF014_25DAF514
  };

  // Compile-time random permutation for LFSR output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h23698838_315F5783,
    256'h9CB68265_38761C7F_0FF3A5D8_8B6C3289_2F7ADC87_1CA08D47_C6B4B38A_2ACC2838,
    256'hA1D2DC7D_409CACE0_9CC31C9B_C5E9F484_D4B48F15_07981C39_B22654A7_34C28458,
    256'h72330D8D_859AECC5_11DBF050_C1AE032B_32ADACC8_427AD134_DE092DE7_918253E5,
    256'hF97520C9_CD002215_E58C5266_8BA0E9B6_5828B43A_EDA6A997_BA8D9D31_42F45531,
    256'h8ABB697E_2B87D9DE_C0A40FE8_405E32D8_8ADE8274_931BD2A6_27192535_2CBE9435,
    256'h61B90AD6_88C8D0AA_23980869_A91DFC5E_5E2FDE16_82EB66E8_19F5CB6D_26481D89,
    256'h86EFE1FD_066C11A6_AAE67712_28DCD2BA_4DC20064_7B1275D1_CAA5CF74_AC6CB644,
    256'h09B40AB7_1A8414AD_9D451AE4_E1246791_E4989BE5_90B70646_6014342A_B6240054,
    256'h9FBC6501_5C122C49_28F18B32_8337D9C2_5144BBF1_970814E5_571A255A_C026B11A,
    256'h16CAD509_058499FC_4EC66CA7_25D55D65_C1403F73_0ED96EBA_0345F860_D78C0440,
    256'h46A7BC8E_E0609B4D_62719EC8_C60836EE_849FAF69_1D6F3B11_55C4F19F_04301B1B,
    256'hC44F35DD_9528CB9B_4A6822C3_E286CBA7_07E34466_0B8C9B78_C8631616_42413755,
    256'h6204CCB9_1D0A54BE_2D518679_E59446A9_0DC6BD62_55ADD926_8DA4A125_1E9969C1,
    256'hE83DA850_D076215A_B1B62169_AD35717B_5F0DB481_3AADAAE3_91374CE4_C3BE173C,
    256'h9D603801_180002BD_ED29ED53_8A964083_064D1018_6C9A0D39_7C2DF6BE_914D2EA3,
    256'h5AE846DA_5A263830_19D8F51D_011D1982_23C1EEC7_9B0B5931_E1771641_30F47111,
    256'hA8408601_6A074B73_A04880E4_22B0E00B_EAF59C65_589BA0DF_024D9A90_91CFC0DE,
    256'h22D07054_28E448A6_219A31C4_FB76E000_7222C32D_038EEE93_DA113629_106A5672,
    256'h08B9E2E4_AAF98BE1_4A30A482_AFDBBDC5_B504F924_D8430D59_1169A3ED_69E88A12,
    256'hA580A312_04D8203D_C3B762AB_85F19AD5_721CC45D_9D38991F_51DFDBE2_1E2EE561,
    256'hAD24994A_A23C7502_D3F6C570_7027169E_2C2C0FC4_055D8FA9_E160948C_599188F0,
    256'h3EABD998_BC0E58E8_D01F7DC2_97EAFBB3_CA5880E6_619796CE_C1C04DE8_4B007907,
    256'hBA827824_06F974FD_5B508987_09AFD9F4_E1D7A002_125A7BAF_B05B1D6E_97CDF7ED,
    256'hF5869420_D5488E92_9B5EC682_C034F046_31D44815_BE429942_4C1942D4_C351AE4E,
    256'hCB2AAC02_2A20F25F_1D2268AA_8D265989_D5FCF814_DB56346E_041F20F5_07B8D0FC,
    256'h12B28926_3C215A54_43636654_1713E099_83A4E6C7_E1165064_54799169_054BFE4E,
    256'h0163F936_1FC722BB_8949779E_94C15F6D_E6777474_73A3B7CD_1301F101_6845AA4C,
    256'hF0895BB3_43B06DB8_68A865CE_5716D842_E2B0A526_2A6C4296_83C20985_BC2F3AF1,
    256'hC476A4AB_95145646_37BCEB81_02C85AE0_7AAC463D_BD3369D9_B92E7FA5_5A492155,
    256'h1FFAD13D_706523D1_E31E2332_3A19A8AC_5A7D8A40_EC254E06_B6C17BDD_3208E885,
    256'h18CE660E_AAAA0D85_5525C917_396481CD_4F3D44CC_4E691581_A9D80C59_4A99A877
  };

  // Compile-time random permutation for forwarding LFSR state
  parameter kmac_pkg::lfsr_fwd_perm_t RndCnstKmacLfsrFwdPerm = {
    160'h872627EE_5DD0CC57_2711066D_4613E16D_FC7AA968
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h3FB98DA0_7716FCAD_65F3E31F_080803CD,
    256'h2623A598_86C456AE_E64DBDDD_5E30D2D4_5743A121_253BC13A_C9F2ACB6_DD51E22A
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'h13200FA8_28BFEE3E_CCF02417_FA68D004_534267F6_0B34A8F0_72E77EE4_859B243F
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h92CEB098_BE6E65C3_59480858_C39611E6
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h58C97FB8_D3E9CC0E
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h7F8FA872_5200C726
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'hB3908794_02DD2531_3739841C_BE832BBB,
    256'h5676FFA8_A19BD7A9_367EE4CF_151668A8_3044F045_8D7234A9_B5467FC4_ADE03FB2
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h13660C12_E3AEA365_38CFCFD9_E59D2187_0A8A7772
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h75BBFD36_BA48E780_D27CD582_540C7A68_FF254EDF_D852829F_ECCCABD4_AF9C9032
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'hDA20BDAF_59FE2AE2_09B8325D_2C8C35FC_960679B1_06A87E59_E6AEB1B5_302D3340
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h10702516_96FBB4BA_169A6CD8_2FAD46A0_A5C04009_BB934C7E_F7B83B6E_40610B43
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'h09FCB9DC_54D42761_37F9901D_09A76AEA_A19DE5C5_79FD38BD_F38F0C21_D6A52226
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'hB6A4A7BD_B05FE921_615BF2FF_984540F7_D43ECE76_B4EB1336_3774ED2E_D45545E9
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h27F6D9E4_ABAC398D_42C745EE_F646C146_4DCA86DA_FD7C7C71_E6058DDF_D871C51C
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'hACBAF441_0F06DCC0_36FCD16F_CDE97D17_1891105D_D895E3A1_D0A19A16_D6DBD8B2
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h0FC9E662_E1E1B498_2B3E8EFF_63890DBE_AE926FD4_68A77EFD_E3DE5B4C_AF4776A2
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'h47BABA4C_9908ED16_BC5415EC_16D28C53_551312FC_EDCF2832_A66CEACF_8ED4D5B6
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'h16177DD4_3B56FA75_4E1F53AD_658193B5_63D9BDC6_D2AEE848_52F0CC73_71ED3A6F
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'hAA516C14_4B34C96D_FABB6F6E_79208A74_F35C79F3_97C4E4C7_E22B7581_848A90A1
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h254B2276_BEC9FC1A_7A5722A9_AACA4DB8,
    256'h4A32E5C6_985A1A64_35118B5F_5F3FD3B9_313116B6_7192D856_DD742D40_E072E417
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hAD9A5F26_1204CBCC_69A21478_19B290A4,
    256'hBB026434_7C0F91B0_CEC93C01_29D85B95_801DBE03_F17E69DC_260A7999_8EFF5C71
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h0B67838A_DFB99A5E_CA671672_CF19BCA6
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hADC1EBFA_B611F19E_7262E0A4_91970E51
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'hB28E7026
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h929EDB06_2B29D3F0_2266EDF1_070C99A8_A8CF6F9A
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'h4A36A647_E90FFAFF_9760F5E8_38BD8E24
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'h13AB956B_106CA713_9A07EFFE_E457DEE8
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    32'h2B6E0666
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    160'hF56EAECF_0E8F01AB_0D3BA124_D3660B43_1E1F88A7
  };

  ////////////////////////////////////////////
  // rom_ctrl0
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl0ScrNonce = {
    64'h43EBF0C5_DE019FC0
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl0ScrKey = {
    128'h73C4C599_518BF192_44417288_93C652D7
  };

  ////////////////////////////////////////////
  // rom_ctrl1
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl1ScrNonce = {
    64'h372432FC_C4D3092B
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl1ScrKey = {
    128'hD6383FDB_A35279FC_BCD2BD2C_1319E71A
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h293AC324
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hF671232D_51E5EDBA_0D0F276B_F0E8A96B_00E81C53
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'h356888AE_5343DD78_4CBA5BEB_BE2A6EAD
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h062D9516_FDD8B110
  };

endpackage : top_darjeeling_rnd_cnst_pkg
