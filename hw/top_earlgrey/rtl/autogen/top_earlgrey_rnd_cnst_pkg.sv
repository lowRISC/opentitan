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
    32'h30D16A94,
    256'h098E681252F1C7741DD6E62190D79F1230D02F643AC42FA70CB942155264F8C1,
    256'h21B7387A0A07DB44FE8C330CA072829F9970F91074501568220E25BA7743095F,
    256'h2C1194FB74487A86B6FEE0311AF608B7123F603C251A36AB2E658548C5420BE5
  };

  // Compile-time random permutation for LFSR output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    64'h658201763C640FA7,
    256'h703F4EAD00959A7196BABDA714F0E5B947B3F17A491F675552019F631CD435D1,
    256'h8EC120344AB92EF33C052BE5A689E5B12943BDBB9CA066D6D757ED3A1C50C78E,
    256'h6A1586814D32D23297AC79FA7DA1A756B9D93EE491E66935A115CA0A38A63A9E,
    256'hC055AE1114355A6CA0B9AD9D9EBB38775157D5F0707DEBE1CE7A5EED58E8F085,
    256'hA8877C7C9BB1BA962E7609A27C1C1509C8E2E8710FD390B2B20C5A3D22AB2C68,
    256'hD084AE824860E09D1E73A88E144465525B74CD400D741609D7E81491D7771CC3,
    256'hA26623840044AC34CAB15FF1A9070B1DAFF72EB72B593004696118F32CF70205,
    256'h95FADF871F06CAB54C652638FE77A42A0A678214BC31E93487E7814816E786B0,
    256'h403761E4515C09A1A6984C43ADA039072A887432B03F03B2959BBF3015D9A91B,
    256'hAD428CD51AA2DB153E0C64B805F472923A6256C4661A86E31091B20A3F02A2B4,
    256'hB567319ED19DA1A80A1575818503042A2528160322E224A9C36926AD2A66E157,
    256'h074D03348C329E23A1BF89223799E181CEE3C8A280CE538C1FAE45C8BDAF0D94,
    256'hC944B09F18BC2942602A94C2F70560BBB998C4D872296249D655E9E38B0524A0,
    256'hC92EA933C706665330CCBC0F2B34E5BC8A04F06413A3949C48AEA8D29B9DBA64,
    256'h4DC2DE9B966D853428A059E1B6CB5BE6B88592651B7960C029240012453B52EB,
    256'h35FB446EB621FFAE2F6A4513C261B8C5D658E661A027B6D8D36E224196A95696,
    256'h8F4F69740CB7166BC26C2B07FB58727F23731E9E45474940484F1EC106203E42,
    256'hA715952427F3B12C76B1F26E71A75DB0DE90AB6DE5C1C93E299AC9198F90BBB1,
    256'h2505C4368C4E3A54E247051D71DBB46F12D4F299F37BF1C6E5821803DB096DC1,
    256'hDCE65DC117D09A2EC13CDF85CE8C4A8638102C8566DC6494C0E00B329789D348,
    256'hE5DD950065B14A47A640BF157A900365E8545F5BA8556A2687E68A01DC3AF226,
    256'h39CF5088A7B750F70AC961571671242D4617C6FD405417027B305464DDB18491,
    256'h62C6336CE192246B732FA50C71BA5A0B96F346ABDC00B68D95A2E5086F4C224C,
    256'h0F259640F9833388106E6F21449579181EC5774135B80A82F64D56E4492ABBA7,
    256'hC9906078836F4791F68395954DEEAA0986D03A4AD797C88635C6587DC84FD030,
    256'hE02BC1243BC44D2EE57752532225FA92FB3D1B084DAAC5AB62FD3B8C0324DA48,
    256'h37E839CEF5A367783229C20472E11C2A502256D23FC10AFC345D679085BE4F5A,
    256'hB27823625783AD172FAAE5A30F73C6C47550B9866C088369510971FD0A71407A,
    256'h953300275CB3BCAA216AABBFA8425E4FA69B6234640250593310178DE02E4E83,
    256'hCAB4102D919404E2104BC7D5620962A6598202159D5BE0117F9D223D61360D1C,
    256'h627018A35A008B4861D0E6178AAF91107A482D106952312D96930D9A816AA944
  };

  // Compile-time random permutation for forwarding LFSR state
  parameter kmac_pkg::lfsr_fwd_perm_t RndCnstKmacLfsrFwdPerm = {
    160'hD91D738A787AFFA424A1E48758D9AAEE61E3028C
  };

  // Compile-time random permutation for LFSR Message output
  parameter kmac_pkg::msg_perm_t RndCnstKmacMsgPerm = {
    128'h7D283F118981787A4631DCC35E5A0854,
    256'h9E0FEB5AC58D44640936BCCBBD10016C2F85BA998AC3ADD9CFA7F6EDCD2F1E4A
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'hB1AC8EA0520D1E942E68202565535CF357B4544CECD50B63D8A077517EA4B4EE
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h4F2F4EB66E1C16646A7BD56D29AC43EC
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h0BEC29248EAED09A
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h61480D9E25EE5C4F
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'hB3E8EFD642C5BB87B4DC3557CFC33198,
    256'h196AC1B513E8FC9DFFD8A0691D9F64D847710ED2E6D9D608824438AA29180AD8
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'hE48303CEFE06DBF199D1622BAC6496489F42AD5D
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'hB46FC99AE645F3DD8F3EAD31DF20485CEC3B1975D7E78D34474B8A3E1EBD40F2
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h81F213FAF8A2D8E27D0E00D2BFF0AC380A5BDE7E8AB3461A9B86823818D0FFD7
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h66C33522317DB4910816E9F35A99F403273CDFF3AD3389C1708A2A7A6DA271BF
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'hA2CB8F24F7E8BB0A0439B0CD362939BB2E0D30A49D0522E9A5B96197D6349A22
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h203BEB21B48E13B127FA42A14CEB82B6610A5457BBF1CAF507098F7022B6F355
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h0C00998FE5D2429B122499F398D73409C6CE2E8C4CC7AB13C648D6F3AEAC01E3
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'h25552FD110DE6F185A80F3AE276DB2416FC002D04B77C626E56477E3DB8EC31E
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h28F496819267FC8761BE9C1AB36495FD7C0CB3ABFF6A4FC7F10263B08FF69923
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'hF5D3781CDC459FE1C6AC6343A98F8F32E989297C02610693700D68B4716EB94C
  };

  // Compile-time random bits for generation seed when no CDI is selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrCdi = {
    256'h3EAC99515E95F75B2F747AB4FD7B64834768D0B0CD8A5828BBF2CD4BAE6862F2
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h011D8AD4C0195D90AE1582AD51E12EB525C2E74DE16A934681A42F3C72492F96
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h8C974099F25B81790BAF31228FC01CBC,
    256'h67C9EA62ADD8EF450563C45144EDF3C3312B7EB88E6B5C614553E6A285EEB801
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'hF5347613C1C980F2B67A249592B3504A,
    256'hEEA248439F4703D603124E3211B0D83A2CE3940F256B3DB0EB494EE8937D08C0
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'hAFBF21AB369D0ABF6E68B959301E3403
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h1BE8EECE2EA06860734991CF2141384F
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'hFFA4CB6F
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'hABC416CF965E23AFE646BBA9021CA0F291B627A3
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h5360CDF714F75BAE
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h96990EB046B67B2CBB2A1859C5C6A54A
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h26E4D620
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hBF5CDB4B6620AB41B0B0E29008CF4BF070979FF9
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hCF829F05B62E1FF4CF4A35794396ADFC
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'h67843D1FB59AD3D2
  };

endpackage : top_earlgrey_rnd_cnst_pkg
