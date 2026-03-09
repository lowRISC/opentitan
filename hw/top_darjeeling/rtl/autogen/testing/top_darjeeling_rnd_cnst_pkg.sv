// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson
//                -o hw/top_darjeeling/
//
// File is generated based on the following seed configuration:
//   hw/top_darjeeling/data/top_darjeeling_seed.testing.hjson


package top_darjeeling_rnd_cnst_pkg;

  ////////////////////////////////////////////
  // otp_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter otp_ctrl_top_specific_pkg::lfsr_seed_t RndCnstOtpCtrlLfsrSeed = {
    40'hD6_C33DCD8C
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_top_specific_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h1DC8_142C9318_69264F01_78643659_85401093_29B22276_355E1273_967C3191
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_top_specific_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h4C339A66_A305E039_830B76B6_908BC88E_CF269885_E094A52D_5437E2CD_45C60D14
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey0 = {
    128'h688A9A20_B68E0D35_660E593F_560F6866
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey1 = {
    128'hA1AD90A5_09423977_40AB78C5_737A2379
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey2 = {
    128'hC2EDE5B2_5EC5514B_680CCAAB_361C3F85
  };

  // Compile-time scrambling key
  parameter otp_ctrl_top_specific_pkg::key_t RndCnstOtpCtrlScrmblKey3 = {
    128'h8E1C5CCC_C121A2C9_5D21294D_190AB75C
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst0 = {
    128'h09C87E42_745452D8_A010A9F0_EF3221D5
  };

  // Compile-time digest const
  parameter otp_ctrl_top_specific_pkg::digest_const_t RndCnstOtpCtrlDigestConst1 = {
    128'h4DCBA329_FF2F7D4B_8A3ACDB3_25087FAB
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV0 = {
    64'hA0806E02_A1FBA55B
  };

  // Compile-time digest initial vector
  parameter otp_ctrl_top_specific_pkg::digest_iv_t RndCnstOtpCtrlDigestIV1 = {
    64'h9BD623E4_0AEC9B61
  };

  // OTP invalid partition default for buffered partitions
  parameter logic [131071:0] RndCnstOtpCtrlPartInvDefault = {
    704'({
      320'hD08F694A5F790581D728BD369D03F8087A60A7F8ED956442C9CFF0F99E594C7307F376E7B2B2FF8C,
      384'h6149B9FF4F5979607AEAD63A44F896431DF745A52C5AF5FDF86D2CE9FA1041C43F145A8BF5BE7640D7AAF2481067180F
    }),
    384'({
      64'h0,
      64'hBA37DEB973D827E0,
      256'h9C47222C695C123916E90F1BDDE834C31D3EEF689E998822EDDEB20732F666FA
    }),
    1024'({
      64'h0,
      64'h5A7F3E2373A78AA2,
      256'h276D9C42B4B5C6539C73A2705A4682BAA1885457797963C3980BFF063FC8BC64,
      256'h2E2904AA8A7090712CF9A372BE9C2B9C1FBFF3B68368C5AFEDCDEE44F5D8D84,
      256'h4C8FD64171EDB20835AEF32CF20B0C620E9AF6C53593DAEC8E3CAA2E495A8976,
      128'hEFF32B59C0A86294D9767FDCB4745699
    }),
    256'({
      64'h0,
      64'h8688686A7D26F94A,
      128'h2552A6AA7830346413591B15ED255318
    }),
    384'({
      64'h0,
      64'hDDF650F1A00008EE,
      128'hB5742826D2CE8D8BB874DDD1DBCA5322,
      128'h1FB5110B0618183CBF722F142EF9FACF
    }),
    128'({
      64'h1F2A6BD606D55F72,
      16'h0, // unallocated space
      8'h69,
      8'h69,
      32'h0
    }),
    576'({
      64'h6FB88C3B4FD535BD,
      256'hE78E601C1704C34A6DFD043E96E1EF76D15C0798EF406091D605165216FD3F85,
      256'h58B183F3D37975B4A9524DE21084A9D64BBA835C10B5E29043022273F7AFBF68
    }),
    78848'({
      64'hCA832DA13EB53FEA,
      5248'h0, // unallocated space
      73536'h0
    }),
    8192'({
      8192'h0
    }),
    2624'({
      64'h28B1AE331BF3824C,
      1280'h0,
      1280'h0
    }),
    2624'({
      64'hEBAA1ACD79D438BB,
      1280'h0,
      1280'h0
    }),
    2624'({
      64'h8A4FE08CE276C9C9,
      1280'h0,
      1280'h0
    }),
    2624'({
      64'hB5A6FD9823EB9F1C,
      1280'h0,
      1280'h0
    }),
    2624'({
      64'hB51350C5C23EBE77,
      1280'h0,
      1280'h0
    }),
    2624'({
      64'hFDEEF22E74536D01,
      1280'h0,
      1280'h0
    }),
    2624'({
      64'h4BEDD6920E68A84C,
      1280'h0,
      1280'h0
    }),
    2624'({
      64'hF9D303313B0977A8,
      1280'h0,
      1280'h0
    }),
    11392'({
      64'hC167C84BFDB86457,
      32'h0, // unallocated space
      6144'h0,
      1280'h0,
      1280'h0,
      1280'h0,
      32'h0,
      1280'h0
    }),
    384'({
      128'h0,
      128'h0,
      128'h0
    }),
    4800'({
      64'h2A24E15352C559FD,
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
      224'h0,
      3360'h0,
      32'h0,
      32'h0,
      32'h0,
      32'h0
    }),
    2496'({
      64'h9521702FCBCF4F54,
      32'h0, // unallocated space
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
      64'h0,
      32'h0,
      64'h0,
      32'h0,
      32'h0,
      256'h0,
      32'h0,
      992'h0
    }),
    512'({
      64'h45515694E825B33,
      448'h0
    })
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Diversification value used for all invalid life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h4177E89F_75139F74_9DE9B374_A3636A66
  };

  // Diversification value used for the TEST_UNLOCKED* life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestUnlocked = {
    128'hF969AEA3_E98FC6F4_892BEB45_8D5B4BD6
  };

  // Diversification value used for the DEV life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivDev = {
    128'h44E79A35_D690BBB8_52739DC1_55FEC8B9
  };

  // Diversification value used for the PROD/PROD_END life cycle states.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'hA9CA90AF_AA465596_5A49D16A_C35F3D22
  };

  // Diversification value used for the RMA life cycle state.
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivRma = {
    128'hF5CA036E_029DFE3E_013F8851_4B08E645
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'hBBA939B1_4566456B_A439FB38_2D362730_ACA45340_F2B0EE60_F25E2CEE_80A25160,
    256'h9D5DDA4A_4AD8C83D_397D1F83_D0345AED_BBB4D7AA_719297D8_3AE6DF7C_A62C4B0B,
    256'hD6EE484A_7EAFE907_9B80932F_7D9EF197_BA49CEEB_EDE8F7A2_6B193726_84CDC442,
    256'h2C133B9D_9A6699B6_C77A2976_1F959810_7C33B11A_C5761C14_981AEAC9_E28F9D01
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_handler_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h6C02B80B
  };

  // Compile-time random permutation for LFSR output
  parameter alert_handler_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h04B86EE5_9F19DA5D_6C93C522_E0AD2A7D_7D645E02
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'hBA3CCF06_D21E5139_60C35528_862DB5CA
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'hC22CB2A4_5AB2E047_CE9E7C9A_EC58AC5C
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    64'h50438289_9FC90D11
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    128'h5CFE3DCA_48CDDA13_84979634_F9E9DAB5,
    256'h35434AC5_AE045437_D6FCFC72_91CC882A_8AC19A3B_ADF19480_8E91FF16_E624B740
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hF1339251_9995A8F4
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h0DDCE53C_CF1F9815_F417227F_6F72D172,
    256'hD5A32A04_F8D6B8B1_02890D10_24AEA6C4_39BF6C0E_7BD61464_7EFA2068_6A9FE695
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'hD6783E30_162258DE_B30E6A97_46B78F2E,
    256'h14C90AC6_7F23CD9A_F63C7BE3_9B526D4D_E8C00BF2_15C10628_E41D9349_69547B9F
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    32'hD6062808,
    256'h41FBBC59_EEE0B265_E2C6C1A8_FE8C1D8D_7098A8DE_068FE962_1076E875_6EEAAF9F
  };

  // Permutation applied to the output of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h3604696E_3B410C6A_88705C0B_06017A28_34502E12_8C0A2300_165D3172_47320E60,
    256'h5F0F8744_4C95681D_9A07847E_59800375_778F0596_023A942B_556B2A83_6199224B,
    256'h7C088249_4A9D935A_4E217371_155B381B_98268E9F_3F7B1356_19745209_1A17208D,
    256'h43783557_1F299246_67866245_1C402F24_4F2D3010_483C1E90_3797584D_259E667D,
    256'h8A6F3E9C_8B631164_7F9B145E_4227796D_9153650D_85763989_813D5133_6C182C54
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for PRNG default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    32'h027AF600,
    256'h4DB28500_37A5DD46_09C57F5F_CDBE0371_7CAC554E_43806E74_AE0341A4_E42FA909
  };

  // Compile-time random permutation for PRNG output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h9196A798_B1899939,
    256'h7280AEDD_A6CC9C1B_9CB4A6E2_8EC2B2F5_D72BA4DB_24D930CC_2042A585_6AFC40FC,
    256'hA4D2A5AE_497D9506_64BF438D_B610BA56_25F58060_1E5AD224_835E4732_A13E5048,
    256'h15660A54_9AB3D55E_9CAC5316_0791F1D9_64B27ADA_21121453_A0FB8099_0DAB1411,
    256'h4CC4DC69_FA304F43_035D3186_CCB5567B_189A36E1_F46D5EF8_A1BB56F1_70901F57,
    256'h686429D3_1691F104_A46C0E77_E04F6B89_31AC9F46_18A20084_26125C06_044E60E2,
    256'hAAD19293_258A430E_E48A8DD1_59EB25D0_6DC3D051_25640F17_C65DBF3B_3080F671,
    256'h690B0B4C_D87AAD79_09000E4F_F5028E9B_6E42D8DF_BF9BC6E9_9BB69876_E61C11A1,
    256'h8BE1ED47_318B3638_7502700E_3E9F582C_59C24547_7A6E17A2_8F3C0015_A86C808B,
    256'h06BCEEAA_8AF13860_52507132_27FB4992_9A08B668_F63820DA_5D65638F_DC79DF07,
    256'h0AC95CD6_A15F0BAE_A486906A_3E2E808E_F282352A_E605C407_BA5810A4_E20A85DB,
    256'hF4B3164F_B3786406_E9F25F0E_0FEE1586_9E6A5169_AAC03729_69B2E5B0_CA989289,
    256'h0D2BC2B6_2568136A_680523E3_D41C926B_30AA555C_337120BF_074AD3FC_7EF050DB,
    256'h67F4549D_0F4AB051_27AB85DD_420EAB59_C1A7C368_77F2C6C2_DFFB1157_7949B33D,
    256'h09536F76_948A63D7_2706697F_8282E0B5_4656894A_BD67A641_E9CC9BCD_453ED804,
    256'h980AA5E4_3542D299_7DAFD9C4_D5CF2E4A_1523194B_1768B6EC_C6CBB332_8D065B21,
    256'h2D3A149B_14B8219C_DFA71705_77639844_68B42D6C_4450059D_6A9A216D_0A30317B,
    256'h67C08BA1_2706A2C7_B00984D4_A1D45C42_C65B06AB_802209AC_55A606A9_D6A7BD60,
    256'hB3399617_9084D2EE_23AFBA0E_377CDA65_45A8ACCE_3939E002_A672DCE9_1BE22902,
    256'hE773985B_E547942C_A0607D16_D109740E_A090D1B0_DD8D0F77_4A78712B_98769109,
    256'h872519CD_452EF78C_E45685FB_6E3C219A_A3A0BC76_0D03AB15_40ADE9BA_0194C322,
    256'h966111EF_C931BD6B_D0F5CC0D_6DE81050_8792EF61_151D7A10_31F97F54_C3514CA2,
    256'h650EE848_BE78A2BB_52547EE7_7199C8B3_80B27603_C320C978_C43C87B6_35176541,
    256'h7906F432_5839E840_ADE2F349_C0A768C3_1E848EAD_C04CD144_AAD5BE51_3C5C318C,
    256'h8D9689A3_F9D50752_2482CF39_A31485C9_8CD33232_1E5B0742_16362597_515AA032,
    256'hAE3C5178_46891132_19A49EE7_9DF76871_C7A59830_1D0C6938_5A58B03C_E500AB64,
    256'h7AE62421_F2210182_2650CDF5_9629C57E_BA5B6944_6E6359A7_613524A4_0F0B5610,
    256'h644AF77A_6271E097_E5F10DE7_C6757A1C_2230E149_A64114DC_7CAB9D92_9F02AF8D,
    256'h31E0B4A2_C3152EDF_121303B4_00553093_E5115170_4254DA01_96EBE8EB_8A85858E,
    256'h562082C7_CAC70818_61393C15_EA84BECC_0064FB2E_DDA20046_252D5FA2_71FE4531,
    256'h9BE3E18C_8A6C2BFD_28C0C239_E5DB96D3_B19D7009_6669123F_8CAF2AC1_4410CC14,
    256'h9A5581A1_63E9DC78_43E642B4_10AAA07A_D9BB5884_8DCA1D90_C44C4A0B_95618469
  };

  // Compile-time random data for PRNG buffer default seed
  parameter kmac_pkg::buffer_lfsr_seed_t RndCnstKmacBufferLfsrSeed = {
    32'hC3482AB3,
    256'hBDCBD9FE_825728F7_BA40A22C_9719C5D7_C160F492_D0E87576_31EBF752_A1E5604E,
    256'h2D6171F5_DBA9EC42_49052DCC_7A4D584D_57AC2784_3EA2A016_3EFEDA5B_24D93F97,
    256'hD62D99C9_60542F4A_1F259519_2E9A969A_885419A9_D57E3651_9FA42D20_EFA348CB
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'hB95D27E7_C60DF80C_96390C01_473E24D5,
    256'hC10332AA_CA1B1863_E87FEF53_63DA4894_C8DE88A9_6DE5DF66_C1652EDE_E0982F5D
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'hB59874CD_DC9CBC64_5D9E02A9_6B998091_1844D3C7_4DE85E05_164B829D_484BD447
  };

  // Compile-time random permutation for URND permutation in BN MAC.
  parameter otbn_pkg::bn_mac_urnd_perm_t RndCnstOtbnBnMacUrndPerm = {
    256'hAD6FD43F_09F0AF7E_9F0BDF8A_866731FF_53129C05_2D7F63C0_653273AB_8F74C7CC,
    256'hB8F2F10A_ECDA4F64_3735F4A4_DC581E3D_78B26208_4C852B10_0F49EBBD_184A425E,
    256'hF890A243_FBE2C341_A8E420BB_CE3CA704_54DB4094_44E336EF_154B66F5_F660BA21,
    256'h6D96CDE5_2C565075_308C92DE_FA51C6F3_C13A553E_ED7DC547_0C076AE8_842201BE,
    256'hF723FCA5_D3BC2E27_8902B370_9B6B16A0_88ACCF0E_87065C91_1C14B1E7_72A18E71,
    256'h456E1DFE_B5D58017_E6B4591B_2AD18324_E05F6897_1A389EA3_957A692F_81E929A6,
    256'h4EB6E1AE_EE9A034D_39BFC4C8_7CB7DDD2_D9AA34CB_6CC25BB0_79B99328_771326D8,
    256'h00FDF98D_8B9D4648_5DA97698_7BD00D1F_33EA25D6_825A5711_3B52CA99_1961D7C9
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h84156D37_CC680632_76F9E85F_AEE129AE
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h80F5B440_DC779649
  };

  ////////////////////////////////////////////
  // keymgr_dpe
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrDpeLfsrSeed = {
    64'h127EC56C_7B0E9645
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrDpeLfsrPerm = {
    128'hF0F14CB2_DA297A36_97CC7832_73E26BE1,
    256'h46773BFE_648516E5_EA707D00_A4350988_9DC13484_EDFAB42F_60E6571B_8D58622F
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrDpeRandPerm = {
    160'hC24919B0_A8A3ABB1_0F563643_F5F40D3B_E1792B9E
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeRevisionSeed = {
    256'h4F3D6CB2_8EDB47B1_5F73CFAE_197DC3F9_534A8714_5D40138D_0DAA41D0_EFE0910F
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeSoftOutputSeed = {
    256'h221C4F25_A8801439_ADC672FB_B9D5B077_F2CD4011_EC5D8376_28672043_36105D80
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeHardOutputSeed = {
    256'hC00220F1_DA1D3249_B8B27F54_0D01C612_6736232F_99134307_9175C6A3_F36D389B
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeAesSeed = {
    256'hD5D0A06E_314F7E0E_FDC7B797_0A3EA735_116A0C6B_28F2300D_F47AC928_7A219E00
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeKmacSeed = {
    256'hBB035F64_C94DEF90_7A59C5B4_75DB2D4D_DEE65528_DFB5418D_8791A405_18626BFF
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeOtbnSeed = {
    256'h091F1BD0_FBAE6741_5FDCA0E7_4227478F_3A0D0E78_F4F82AE0_04FB322A_9D35FFFA
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrDpeNoneSeed = {
    256'hE30FC86D_8EA37BB7_BFF6C665_3CDA8E06_6B989FB2_BD83BEAD_CF1AB871_270CC1E5
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h37545255_EEF8BBC5_6B206E00_8162473A,
    256'hE6CBD492_6F66ADEA_B5DACECE_DE39F5AD_96335C47_09F70E34_60D37113_EDDDAF0D
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h2FEE3DFD_E1D06699_84352FF4_E13B0CA8,
    256'h8B5A2EA3_8DA2B1B9_D78968BB_CC29D9A9_B33196D9_8B9EA0DD_8511D589_4D815064
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h1F408227_E59F67B6_DC36409D_3CD85FEB
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h1EE31992_6BE21C68_2953B498_F0978818
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    64'hDB9932D6_137CB3FB
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    128'h78B95693_33EFCA33_20C437EB_4476D752,
    256'h9F0A1A2D_89490EE1_9990013B_8134FD56_370AD753_F4DEB0BA_AE6823E6_AC7059F5
  };

  ////////////////////////////////////////////
  // sram_ctrl_mbox
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMboxSramKey = {
    128'hC166EAC3_85803F42_E8DC3259_0EEB66EF
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMboxSramNonce = {
    128'hE8190913_01E645F7_4C60EBD5_50B4FB39
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMboxLfsrSeed = {
    64'h59D045EE_62C7DEA7
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMboxLfsrPerm = {
    128'h16D1CD05_07F6840A_977164F8_198C5EFB,
    256'hA69BD30F_7C50F239_B042AFD7_BCE998E3_2E267C8B_0E08928D_1FE856B7_77665902
  };

  ////////////////////////////////////////////
  // rom_ctrl0
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl0ScrNonce = {
    64'hDB9883CD_A8C2D0DD
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl0ScrKey = {
    128'h65578D17_3D15E674_078F0C57_31937EB1
  };

  ////////////////////////////////////////////
  // rom_ctrl1
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrl1ScrNonce = {
    64'h950645BF_C40D611B
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrl1ScrKey = {
    128'h8B53E427_83D6C11C_F5392531_9FD215BA
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h2EE4E73A
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hE4D39258_D469D5DD_DFDFD400_F8B91560_44B28E58
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hF8260EDC_EF146342_614F489D_F2A995C6
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h1CAAFB48_C18FBF25
  };

endpackage : top_darjeeling_rnd_cnst_pkg
