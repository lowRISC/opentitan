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
    40'hF45DEF7861
  };

  // Compile-time random permutation for LFSR output
  parameter otp_ctrl_pkg::lfsr_perm_t RndCnstOtpCtrlLfsrPerm = {
    240'h5D294061E29A7C404F4593035A19097666E37072064153623855022D39E0
  };

  // Compile-time random permutation for scrambling key/nonce register reset value
  parameter otp_ctrl_pkg::scrmbl_key_init_t RndCnstOtpCtrlScrmblKeyInit = {
    256'h6FAF88F22BCCD612D1C09F5C02B2C8D1FDB92558E2D9C5D24440722325A93144
  };

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'h79EE911CE801484BA8373086F9DD4EEE
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestDevRma = {
    128'h03A0B091DC41D062DD10CA2D7B93136F
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h0EE2A465FD4DABCBD877AFB6BCFEED7E
  };

  // Compile-time random bits used for invalid tokens in the token mux
  parameter lc_ctrl_pkg::lc_token_mux_t RndCnstLcCtrlInvalidTokens = {
    256'h699679EDD5369F11B49BAC9198BD1FF344C5DA2242D290BEDE094CA8F1435F85,
    256'hE0F7489A309CBE57B77F07FF3D7297200D5AB25561AF49C696466A983E534682,
    256'h6A43628219E5A91389B9FE0D3B818E46CE7D846469A3B8E35A6BD38295BD2FB3,
    256'h66B3D62126C75EEAEB93D32F5CBC77463C91917516D51A2FA4400ADC2669E253
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'hE10023EC
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'h74449A374B5678FFC0A1C18FB47BB50486CB4EE4
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h3635D1F47C8F05AFFC85F7D889ECD94B
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'hC87B69111A24D5E4442BCFB7032949CC
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'h48BAE844
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'h46B0E5D9F9E80FCF3212FC76A2B6A11D2F332482
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h0AF06B42350BB6B68440934DCB834F93
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'hED204633871CB178192AADBB7C918ACB
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'h33A4AC96
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'h3480D1896C7FF9ED5941BD125C6EB18772E220F3
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'h8E18EDEB46B20763
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h05CF6536A2EE3E49D22A36FA59EA2C46,
    256'h20D062F69F5F3209DC203EE4C87FF199B2AF013B1ED4E0395175C5DD94E29D06
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h57EC2E416728B1FD9D00A60C08D538DE,
    256'h2C75CC325A65E95B98BAC182F10EEB4E52F2A93D22D3F24C51D1A7F1A387B5E7
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    160'h5147F1EF84F4B3A9D281437D77F970022C91C1A2
  };

  // Permutation applied to the concatenated LFSRs of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_perm_t RndCnstAesMaskingLfsrPerm = {
    256'h8A88993A824011121A5E9A4936802793375F2E640110219E6607524D79684743,
    256'h5A3B257F67298E72469C239506756B614869422C91506A7B76733D6032714113,
    256'h2439704A0B908B28977C4B1455841C89569653095D3E0E2F1D150D1F8F511792,
    256'h048D4E3F9F1B83742B6298770C26226E450F6D356F4F581E7E784C6C57187A5B,
    256'h86943300030A445C2A65597D818719023C8C1630639B2D31209D340508548538
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random data for LFSR default seed
  parameter kmac_pkg::lfsr_seed_t RndCnstKmacLfsrSeed = {
    64'h2E658548C5420BE5
  };

  // Compile-time random permutation for LFSR output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    128'h60A70D8AB7859F7CE38655C03F06FAB9,
    256'h6F537D1A60649431FBCFF556A6B606CBF4C8790C3835380A89B923B2DDB46112
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h515E0F5E7B6B69CF6CC634475AA9B339,
    256'h997E783B84E6F85F09204CF1D2D3D98A09D296C81B0E90EE2175DCD024CBF2A0
  };

  // Compile-time random permutation for Storage Entropy
  parameter kmac_pkg::storage_perm_t RndCnstKmacStoragePerm = {
    64'h27ACB59C6E3CF10A,
    256'h86272BC1428DA79A1EC03AAD6928012919040D3ABAB4736C30F424A243F9F2AF,
    256'h97476646C96684038AF33C0EAAAC6DB4E1A98DCBACA97B9D6DAD9BBA6412382A,
    256'h362A452CF151D6BC12D9085C26BF4568A926144206D8878787F97837764CF071,
    256'h2CB830569B02010D15A05B7F5DA649C12A938AD65B8D474296A55CE25A62FF5A,
    256'hDE391E7F26A388EECE1F8531CD4B005C975966C6288B61453E9F88F603B2A79A,
    256'hA5449F9BA9AE08B011458CDC631157BEB974C6323A9F62EC40D646095C446DFB,
    256'h66122715FCB36D5AA13AA68419D17A8FCAC9ECC3B04E1A445A596FEB7E42C02D,
    256'hE81C70AF6959D8B4962668C5BF5DE615593E210599B0D69BEA71B19E5765422C,
    256'h6A4F509176F8C05E91A10B332F16D61809C310A402B751F23CE601542BD0D465,
    256'h44C3DD1D6213CBA22657D6A4C4EF0E71F880C79BAA0804EC8E6400331D3F4601,
    256'h7AB31226D7845F02160A6E2853DE5BB54E72A378AEB167C283ED074416F71D13,
    256'h79C00B6CAB78B06C228F651173B68258B0300CD2B498774479044B2522BA93D0,
    256'hD9F5AE75D25AB00D6B57F66F0A572CF8B0FC9A60F2DCC59D48055614B0AF75F6,
    256'hE31A5DF829544398E9C8777FEDA2B43B36F1E37547356B79C2E127D75BCABE1F,
    256'h1505F2091923A94993BEEF020AA402AD1772E27EA55890673DB0F2861B5C0F87,
    256'h81690C18242A85281AF3208D872948165C602DC68660664F9BF12D5341D85656,
    256'h23293329DE29A236ADB2B1C2A988163B9B9C4CF2AC0A28F8E538C1F1C85C10E3,
    256'hC0D997C26B82C24B99E59BA9C6293174C2E46598699415A498454904C647A0B1,
    256'h8D9688A7D1BC49DF7B16816B31CA5A8C14A50324BA9E0F1312EF4CC332F2AA0F,
    256'h0344E6712412E13DBE0641305EA26A4442B974C452981A2D6E16EC6C5032CDA4,
    256'h18467ADCF67581525F0025DBBE5724A21D5ECD0139B711714931ED24AD682D58,
    256'h3F89C390E863CE98BC9193883739F3152344850C7629CC2EEB68C6F44604B669,
    256'h010A2E8C9128582EBE89D74923688EB0B557C3497532E6302A65F8BEA749B4A9,
    256'hE65D8C6334584C8945860069651C12874D29E776BB01A645B14A47A8EB302F48,
    256'h2117A900365E8545F502C556A2D07E622BD807885C36268639CF5088A7BB90F7,
    256'h086661571671242D684924617C6417568B40541702E5305464DDB1BD612458B1,
    256'h8CDB3864891ADCCB21431C4DE6826A4168A8411A5E1FE2DA36568B9421BD3089,
    256'h303C965903E60CCE2041BB5C851255E4630E1EC5774135C1CA82F64D56E44928,
    256'h23C3099060788352F792BF7DA0E565537BB169E8986D03A4AD797C88635C6587,
    256'hDC84FEEC40C38B182B362435004D2EE57BA5D494C8897F12808F46C2136A81A0,
    256'h84BF4EE300C936920DFA0ED49CC7DA367783229188472E11C2A5022541E3FF1A
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'h474C873C2749FF39E3504186B0DB644CC26BB28BE8CF99207E34AD136638835B
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h832242106B2FC62AB3CD9EF2DB8F4FCF
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h891C6D67AB1B45A1
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'hA6F667F0B6876FCE
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'hDE2EFE2300DB1B55D6DAFCEA7E4F5C94,
    256'hA6903C5E74B53389854B04F0B46B1C0E0D319812B828FF567A26C9EE9DC58A41
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h3FF4BA4AAC17146B80A4EB60F0E67BB45034BBD8
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'hC6CE2E8C4CC7AB13C648D6F3AEAC01E3203BEB21B48E13B127FA42A14CEB82B6
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h6FC002D04B77C626E56477E3DB8EC31E0C00998FE5D2429B122499F398D73409
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h7C0CB3ABFF6A4FC7F10263B08FF6992325552FD110DE6F185A80F3AE276DB241
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'hE989297C02610693700D68B4716EB94C28F496819267FC8761BE9C1AB36495FD
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h4768D0B0CD8A5828BBF2CD4BAE6862F2F5D3781CDC459FE1C6AC6343A98F8F32
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h25C2E74DE16A934681A42F3C72492F963EAC99515E95F75B2F747AB4FD7B6483
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'h312B7EB88E6B5C614553E6A285EEB801011D8AD4C0195D90AE1582AD51E12EB5
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h8C974099F25B81790BAF31228FC01CBC67C9EA62ADD8EF450563C45144EDF3C3
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'hEEA248439F4703D603124E3211B0D83A2CE3940F256B3DB0EB494EE8937D08C0
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'hAFBF21AB369D0ABF6E68B959301E3403F5347613C1C980F2B67A249592B3504A
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h4E5C2CE9EF80BCCE0D147EE3FFA4CB6F1BE8EECE2EA06860734991CF2141384F
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'hE85D23C884C5845D25CF9AE43F1EB798,
    256'h2AC2C0C2054167D74E4D1EDD52ADD7D74665FCD3E7FF977DD899341F621A0FA7
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h3B117BB7ACC2E7634F6EB5113499324F,
    256'h078D98D89ED7CD6BBA6E64EA9E65846D8CD3B229D605B329741D5E1B21AD35EF
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hD59C22DEA507142E4F820C738BE5BAE5
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h94456589D6254DC6F598CF6FFF997209
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'hD341D4F7
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h5EFB31EB36AC1C5683E9F1D8496142470D1B85F4
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h09FE6DC4A2E87DF2
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hA7010CFED0F677E82B45032DC7BD4F8E
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h4A9755EC
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hA880323532CE8D1E503357BB83B2F643FEE2C17B
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'h9779E3B8F2B84B85940A6A9D8E80E9D4
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h6B9117EDF0A952A1
  };

endpackage : top_earlgrey_rnd_cnst_pkg
