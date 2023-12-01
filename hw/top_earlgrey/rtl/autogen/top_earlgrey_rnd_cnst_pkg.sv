// Copyright lowRISC contributors.
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
    40'h57_1EAE0FC6
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h4642_9E4882D3_5CD9E224_C7CE0431_6384661A_9823D66D_D8140251_C455C419
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h23D532C0_AB44E1E9_2CCFEBAD_AD9193A3_EE4ECD8C_032462B3_E18549CB_1E70D5A8
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h3DE6673D_2C1C0A7B_55176264_E55C329C
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestDevRma = {
    128'h8AE4725A_EAF67281_50127AC7_55D70063
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h277642B5_309A1639_90B966CD_494444C3
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hBCDF8087_B7FACD65_E9654CD8_5BC66D10_208C4FB5_1B97BBF4_D12C378C_CFD6A5A5,
    256'hBF3032DB_51FA1EB9_2F6CE10E_90F9C5C0_6F733DC9_11A321DD_4C0AC240_6D467215,
    256'hDAB3F2B5_4A52E672_8678AF07_18068E34_4D2EAE4D_73C8FA54_DE8AA4A4_F258F3B2,
    256'hA145FD19_50AE55D6_93E57968_117E66DC_634155E0_F8150242_862EB20E_EA9A1F75
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h44716551
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hE9F28B4F_1248F60F_B6B00DCC_B7BB9AA1_22CF08AA
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h28363AAA_0E93D45C_423690ED_05BD1E71
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'h0F22D109_5889FBD8_A7B57FB1_E11DF367
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'hC1C1EDE3
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'hEF325022_04A4EEF4_FC4A64B0_730C36D6_EAE6C57E
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'hD0488805_541166F1_EC8CEB42_692B089A
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h6F99B1A7_AC084224_ADE46129_80D48E6C
  };

  // Compile-time random bits for default seeds
  parameter flash_ctrl_pkg::all_seeds_t RndCnstFlashCtrlAllSeeds = {
    256'h6493A50E_EDBAC6A4_6B7A8A9B_2C7AEC92_F39E4947_8C398C91_DB184183_1B1F5C82,
    256'hA556096F_FF6175FC_10F93979_2B444E52_1D4711E6_4066908A_DFD5918F_8C563C92
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'h184F1C76
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'hF1A47636_25B57610_6958727F_C5F61944_EEF20874
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h8055B24B_5F3B3EA7
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h34693A24_A552B718_DD0B9D04_BC342E81,
    256'hEEC75887_E1FF08A9_4DA3DCC8_1627F591_4EAF845B_525DE82F_3B3632A5_FE03CD66
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h352C351E_B2238AC0_C93B4942_BD9DCB5C,
    256'h07989ED9_0631D455_531EA17D_3E04168F_2A833F8F_5BFD9B41_CCBB98AA_79F5AB81
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hE9F0EC4C,
    256'h712146A4_AB60DA8B_656EABB0_B3EF6E9B_197CE582_FC9B5965_D697C23B_EAFE8389
  };

  // Permutation applied to the concatenated LFSRs of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h1A695301_8D0A1F40_7A46869E_434A6366_73717976_9406249B_4458057B_04650F30,
    256'h41707D0C_345E0D6A_67573B29_276B2393_2261914B_1D78971E_873E2C35_1337959D,
    256'h4F25314D_387F1081_92886E74_5B4E092D_6D485582_998F728A_856C5C02_9C1B3A68,
    256'h64214218_5F8B2089_50840E08_2F629F47_8C392A0B_28153683_037C1907_168E7E75,
    256'h4C6F4980_3F60541C_9833322B_3D5D1456_7745009A_26905952_2E961151_125A3C17
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for LFSR default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h4645AAD1,
    256'hFB21C181_24635E3D_50A88F68_08045627_AC18F377_D9071BEC_A6F194EF_96F3E535,
    256'hB58F2ADA_D82B175F_E9EA1C32_6A6610C1_117744DE_61CCBFAB_D3E1FDA6_67E04082,
    256'h478C14DB_070A6129_BB2945B8_8DC6CFCF_2AE02F47_010CB666_A5E22D33_20F89CAA
  };

  // Compile-time random permutation for LFSR output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h7C29AA25_31B1DC68,
    256'hBD06A85C_CA941421_0EE2805F_56079C3E_3D516461_F256B78F_752D61C5_1404697C,
    256'hB8451192_DA2365D0_46641C94_D92C6790_C999B524_26DD2424_9E986EA9_C1F69FEF,
    256'h11100B22_16331A5B_28A5C09D_F9A28BF8_225E81D8_9B19CA72_E686C618_3FE03A5C,
    256'h7D035050_29923404_00CA783E_5158A22A_1A52B6B2_7CB7C8C8_745EBC97_7C771090,
    256'h6980B5C5_20C252AA_828DA53C_059A2007_FB8CB355_8ED30C91_85C2A674_D76E8570,
    256'h48C5735A_B49C4B08_1D1698C2_2C468255_0D125D59_61E16589_CBEA4978_9D9538DC,
    256'h68C167AC_9891C595_E155A9A8_F6C2B52E_AA7C0CAB_A1009BE1_2FA0CE7A_5AE9C281,
    256'hE3B20C80_98CA40D3_AD8BD385_C9BB4338_51681407_55C4CB50_EA30AEF9_981EE73C,
    256'h38B32931_48155AE2_61B1002B_5E6B5E66_5D52C465_AA5FA659_CCD266CA_E3A56FB4,
    256'hDED06197_2D97D139_5EAED232_EE3C622E_6305C2A5_6210FF00_3C66BC30_06C1A373,
    256'hCD90758B_9AA48B0F_8A1AE180_1F8D1198_2E326093_22BD912B_EC38DD77_C813331E,
    256'h6A4BE2D5_185EDBC9_006A8C9A_08896C5D_1E5268DA_4A1251E9_B697DBF3_DA740D07,
    256'h6215871B_611B059E_762A836D_204EAA4C_70E44DD3_3B9CEF3C_AD503801_180002BE,
    256'hC029E393_89020C20_04406189_E724E5C7_62E804D2_81359EC4_6D81BDDB_B3017A8B,
    256'h11D01315_C5EF37C5_934FD649_65E0BFD0_4C451C90_A2E0216A_074B73A0_4883A312,
    256'hB0E00BEC_359C6558_9950DC6B_4D8246A2_EF6E4B41_C1E79F51_2298861C_4FB6D147,
    256'hA7225944_E3B963E6_844DB904_17A19C9F_AD48412A_ACA1EB26_7B2908FA_BEDC13E3,
    256'h87F50C35_5F45A60A_A2F02228_4AC6C28B_F8136080_F70ECA74_2B1AE557_21CC45D9,
    256'hD3B2F1F2_8DAD9E8F_E7201C0C_5DB7F235_17704A15_A5A1DB22_495086CC_A1550E75,
    256'h0474894A_806D9C62_29B8911B_F52D8D16_0B609FAB_4D86BD5C_5C30D69E_1C2C0FC4,
    256'h055D8B68_C1609488_199188F0_3EAF6B58_BC0E58E8_8C1F7DC2_97EAE8AF_CA539986,
    256'h5E5B39D6_EE37A12B_21E41EE8_EADC901B_E4C3F713_42250BD6_AC67F127_5E6F0849,
    256'h6C26AB9D_E9E5BB16_37DFB7D6_1A508355_223A4A6C_EACE0B00_D3C118C7_512056F9,
    256'h0A650930_650B530D_46B93B2C_A99008A8_83F0BC20_899E6914_99662757_F3E0536D,
    256'h58D1B810_7C83D41E_D043EF0A_822498EF_4569510D_8D99505C_4F82660E_6C7E116C,
    256'h66454799_169054BB_24E0163F_9361FC1E_2BB3D497_79E94C15_F6DE6777_47473A3B,
    256'h7CD1301E_FC168453_3C2256EB_A0EC1B6E_1A2A1973_95C5B610_B8AC2949_8A9B10A5,
    256'hA0F08261_6DDB82BC_711DA92A_D2451591_8DEF3AE0_40B216B3_5EAB118F_6F4CDA76,
    256'h6E4B9FE9_56924855_47FEB44F_5C1948F4_78C788CC_8E866A2B_169F6290_3B095381,
    256'hADB05D32_08E88518_CE660EAA_AA0D8555_25C91739_6481CD4F_3D44C9A4_5606A760,
    256'h31652A66_A1DC9710_DC08C135_ABAFB4E1_6D9C64FC_6A130E94_1A3705BA_DDCB451F
  };

  // Compile-time random permutation for forwarding LFSR state
  parameter kmac_pkg::lfsr_fwd_perm_t RndCnstKmacLfsrFwdPerm = {
    160'h721AFDFA_782F01A3_AE1DA865_9A12DF62_471BA846
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'hF82671D8_35948217_304A2BFA_0239682C,
    256'hE7ED30D6_AB769BB9_609F734C_59C7F322_AC991DE4_7B41B83F_5408A955_C113F6FB
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'h465EFE57_AA3B59BD_6B0A4021_6363420F_041ED29A_965B68FA_EA3E59D4_F2E2A0B4
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h2EB9A8C3_AB227B50_766D2EAE_C89EB13B
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h07E9BF4E_E4278413
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h6D42C85E_456F3B26
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h67DFF577_9DF3AEA6_1CE14690_B285A917,
    256'h1EA43910_237CFC1B_0A2C8682_D101F870_F6ED3352_3272882F_C949BDE9_AE8555F4
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h341C41F2_9ADF4058_A907F3EA_297C295E_18DBCED9
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h576CA8A8_225C8E17_053E44B6_8DD7822A_6859F2CF_52A55FD1_81B082D0_3C583756
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'hF11AA5B3_7F9544C4_AA90EB97_E1C0F808_6F627A28_1C5681D6_566641EE_CCCC8887
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h6AD113C5_0AD1BE4D_94DCE8FC_A54128A3_860AE1D3_493FBEF6_B9BA5DFE_4463A461
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'h5EF46762_A794A8C2_597E69FB_259B9619_14CD75BB_FD36BA48_E780D27C_D582540C
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h7A68FF25_4EDFD852_829FECCC_ABD4AF9C_9032DA20_BDAF59FE_2AE209B8_325D2C8C
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h35FC9606_79B106A8_7E59E6AE_B1B5302D_33401070_251696FB_B4BA169A_6CD82FAD
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'h46A0A5C0_4009BB93_4C7EF7B8_3B6E4061_0B4309FC_B9DC54D4_276137F9_901D09A7
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h6AEAA19D_E5C579FD_38BDF38F_0C21D6A5_2226B6A4_A7BDB05F_E921615B_F2FF9845
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'h40F7D43E_CE76B4EB_13363774_ED2ED455_45E927F6_D9E4ABAC_398D42C7_45EEF646
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'hC1464DCA_86DAFD7C_7C71E605_8DDFD871_C51CACBA_F4410F06_DCC036FC_D16FCDE9
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h7D171891_105DD895_E3A1D0A1_9A16D6DB_D8B20FC9_E662E1E1_B4982B3E_8EFF6389
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h0DBEAE92_6FD468A7_7EFDE3DE_5B4CAF47,
    256'h76A247BA_BA4C9908_ED16BC54_15EC16D2_8C535513_12FCEDCF_2832A66C_EACF8ED4
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hD5B61617_7DD43B56_FA754E1F_53AD6581,
    256'h93B563D9_BDC6D2AE_E84852F0_CC7371ED_3A6FAA51_6C144B34_C96DFABB_6F6E7920
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h8A74F35C_79F397C4_E4C7E22B_7581848A
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h90A1254B_2276BEC9_FC1A7A57_22A9AACA
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'h4DB84A32
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h7CB60455_500E897A_15A977BB_93DBF111_9835CF1C
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'hCC69A214_7819B290
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hA4BB0264_347C0F91_B0CEC93C_0129D85B
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h95801DBE
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h4093FA68_A3C595C3_DCD2AC19_972E33E8_49B6BFC0
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'h8E7026D0_E5DCE9E2_65A416A8_12231CFA
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h76E3D982_F8FDCEC9
  };

endpackage : top_earlgrey_rnd_cnst_pkg
