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
    192'hA6112E5321E035050F0B70066F2039B08B09674190385884,
    256'hC51B3DEB4F1DCA4B9F2E89C605D75A28E9A70C70C2200484538402E41C250336,
    256'h24918045A0721C8094005F3459FF4C4B0E3A41DC2BA17139F9A516DF872AD441,
    256'hC4AA96A4A12534D3AF527B14877A9F0DF3B02062AE3D910BC5504BB1CE62E018,
    256'hFE6AE7282003D1D07C52C0BFC00B6CF4132C2E21E87A4E6C57ACD1092BE35DD7,
    256'h395BB6B3070C0981A88F65B1E2B1B671415F71997811F104A882D86CCFA0EF77,
    256'h6B75D624008E3D9AA9B51527CAB0AC838472BD213220880225B4158CA7C85AAE,
    256'hD42422402E6C3E6389037B5712CA61A741ADA4533AF09AAB555E5110AA7F3520,
    256'hA84271942E61B12453D1848B0D64CBD970642AA1540144F8542A605501EEC895,
    256'hF22C6952D5018656388F0690AAF2F0F4F214289C80BEEC76485762CE67B51420,
    256'hAD09506817D85957CA5EE0A2E8FEF0036850966E24AE2E3C28DE2284669A67FE,
    256'h265376C85688E3AFB8AF3256427AD8834CA279C4556402D810221C59AC135540,
    256'h2CC391451E79A7B88D3A4BD551818C34C70441789E0AFC28D2E6D56EB1F525C7,
    256'h33A8774DE3F373425B98A8CC12F958B6674E6581BA782CC2A934F3B620D224EB,
    256'h4B8574B4A20862A50A65D0778C3B1E1F63F65E4B8118BF0B1DCA54A28D1E6329,
    256'h6143B184B7D904E62BE952BC5BD23B19B5B96B21E689915267CE61A1675C5540,
    256'h50D588903481A9C6D91F1901FDC043E686CAE7A98DD64AC5176F0A90DCEB883A,
    256'h91488963ECDE6BAB7B3778852A08B075361D359A5977134E0D60213D828962C4,
    256'h0911BE07B4B80D9E36B5814BDBEC5D50C1AACF04C726D61259D55941828ECC88,
    256'h767D4931B2A697D150E2923F7A5731B45FE0D8640F57F40A9CBA154356E70316,
    256'hC6BACCA663F4A197CE27A1471D86C7B09119C792B41381583FDBF82B26CD54BA,
    256'hDC067C59CD1C3D0891AD6ADC61686DD4F07880C23C4A3BE6E6EAEB13E30011D6,
    256'hDE3221BB1490709E8D893E3A5CB598B08A9558B6E5047A59778650C610D39017,
    256'hB283A532884318C541C141D1729D9C18A90D4062314564E185221F6B4B7498C6,
    256'h03EDFE10EA50739DEC1EA265A1D912A15A09C701589B679EDC11BA6CD69D6960,
    256'h0749923B2D21C70A56C3F929A14E9A8DC6CF0BEB314BB264F9178ECBFC34A252,
    256'h333A021909E0E1F92F9F7B17832464C44BC0681BC5D1CD8A2E70DCB8DB3F5F22,
    256'hF8B351AE9EED82EBD14980ADBFC028E48AA1793451E96BB95A98C6F70BD7D202,
    256'h4E02B488C9271A9F047EF4421DFF5FD2D2EC42DA7B07DCDCE913F7D4C23EAC24,
    256'hA2C084CB1709D20248F758081F83763846D903CF87028A937063B92BF43D5BE9,
    256'hC95C12D8064146B40FD6D63B580CD46F87C9316FD476EE7B2AD85FA3F5EC24C8,
    256'hD502EA2DD9459D8824F1B27A1CAC9D8623136DA4A00C909A099A6D736041F403,
    256'hDE4918304C9BA325169198A3202F16DC14FC4D8D059CDB352C0394DCDFA99081,
    256'hCD4C5C4155A8E4CE3F0661A63F80FC7317A2EB994A470F92E92F031D9DED0582,
    256'h004E0481DE2A6CA57F0D0DB55CBF6404F4C4BB7E47505CDC39614CB1A515D432,
    256'hA578FD5E7BC7629563CE78EC42989D46351610E5DE38C75DC9196C5F8A23906C,
    256'h8FA7B716CAB6877967DD324E4E9108B8B7BEF3CB25229B0392631345A6691FAB,
    256'h0C1D6ED6053BF008599A5A28B24DE5C39BB54E64910BB859AC98735FB5C1008E,
    256'h3AEF4F8C5A453729DC2D58961304383DA9BE85B56F417D7D6520A61B4D265AAA,
    256'h4C7D54357252D317DA9F121AF067BF86991A574B326B0D4E3A004CFE825721B4,
    256'h02285469938198E4A0F3DC075953C4154594A12F618A0943FC374EB442A72704,
    256'hF036E680BC6758427FCD67F770ECA9057105DA2F55D49A4F4C623B8C6BA863CA,
    256'h5A46AAC6B0B7714255EEDD5AA1822C45C76F51A9471F7BF40FD8A32F5C299CE2,
    256'h95491641AFEC0817349C0E4560DC31ADB2762D4ABCCCD538F1372C4D24BA6468,
    256'hE08F833CA7D68DAE96245DAE48160CB3D74DD7A04D8513222AED33D332EE3B55,
    256'hADA22FA3883F6BC93C31D38C0A04A05A3005F26365D108C0B094F589A3F0F2B3,
    256'h4CA29E4594374643CBF73050C0BDBC5844489DA3D8B0408A4128ABDF1BA744E5,
    256'h9C406D962C1836CD851BED83B65A0938F87200E842AD64A214EE18693AED8453,
    256'h740C2035A495781D884F28465977E41F2F88687760ADDF33F82D6E1EF2A2FC52,
    256'hED869FAC54AB5AF8F47809AB1B4C469D6BDB2870C84EFE1DBA23B68F3FF6EAD5,
    256'h9853653129F65BDCA9407C95DC1132178656C0FB906BC144B8774AE18CD2B338,
    256'hF6DBE2841A1520A45AA8510F2D84D564773125407C08E867AE2C7CEF92CC0766,
    256'h84CD118DA9656A65D105BA52A76C7D710B15E9E5289274E55C65DA3978E2A88D,
    256'h893F68EB7E194A4D7E6029023B3080C8569BB042389EA1648AC32C9E7AC9516B,
    256'h14A942C917411278CC46668CF5E43CC68CE64852E49FE2A09C17488ABA3E9292,
    256'h903476E2B7676A059C0280CB9B5418231EBB9E676C0D493E0026EDE5D4401611,
    256'h1D722509ED18A26D00A0A0C17B9A113B1CDB708BC7F57DED125BED05A342B13F,
    256'h84E4E44A93A2C7A6CC573A686091CF3AC241DCEBE615150D21A197632C923D12,
    256'hC572F465B461BC88E04A5EB562122E4644490B2D64960B98249DBA5A76919A29,
    256'hD60B4AB8DF12FA7EA612B180B84BF0BE42526E955E6D695DB2A8C699B1629949,
    256'h4AC3A9759678C0169528F125A24D08B1DD92C0193256CA9547924B1385E48308,
    256'hDEAA00367445E82A27D75540B0AB6A37C1F9445C2C03E21B86627684E79EB08A,
    256'h5393FD6743EE1466B0B5C4CE12416BA1324C61BE2906EAA8BA03506E03029835,
    256'h189BDB1DB1C2B091169638CED9A199131AEE66F32871C46F1A04D44176028AC2,
    256'h146ABC1FE96D8DAAD4B92106F66149381E25AB203E30733A40AC28371E242C49,
    256'hABD4618B87B8AEB68E813597F2A173CBD49B56D2264A8479204CC188F083497D,
    256'hE4D7E7D907159AA67B98DA7A1306D01D52BAF37CA434D70CA87EE453F5D940C1,
    256'hC2C60573612194009A2EF2BEE93A994E4425FD1A80A7A5B04266A80D42117E4E,
    256'hF1803226D9226FE835A89CE3EA8DCEF83114C6208E2E28E0A9A042560F0FF634
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_prng_seed_t RndCnstOtbnUrndPrngSeed = {
    256'h33ED52464E2B61AE221D47C237D9733808A6753552F9C148245FA1D975142696
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'hFCD925B97A49122820BD0D8CD3C1FB66
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h6492517EA54F9503
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h01531F43F9B9BEBA
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'hC2F72286C6907887CDA236773FEA53F2,
    256'h71B9838456997C73F55509EFFA8ED6D9182DDEB2D041EE312281AC309B140976
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'h1E68513E67C5621D93C8F9AFC849BD4D81A5396C
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h012E4928758C1AAF53D3C0CB9FC2D765798352E4515270A4CA77D2BEA52D1701
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'h2FE8EEA1A03465B766B01B4C0E74C6CBF137C0A40B52A1EF2B319799F7D5B8DA
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h1D093316313CDCCC59385BFF8DCD9D9AAF9D5F676F39DF99E446B9DB0E474666
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'h59AA0ECB9FD806EB4E3DD624886B16B0EC0798CEA93F582A0833BF0B2D601877
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'h455991A5B63A9E7C797D7F8FBD30DD453E8D794C79F7004572F75E0120178ADE
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'hAD54E9CE434C027A8E39EDE57BAC202C0B1C84A4C098B0596448ED209233AF28
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'hD01CB28DAFE4A5B4C4097DA0FD1DA0CC3EEB3128D06F320B93F0AC65AA928B5B
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'h6B4E1FDFE4CAE1441E8D5A25C611F5DD21D103BCA371A0989313BAD9D637216D
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'hCB97F3EF8F47801882CBA98F3A427E0F36596BF17DE242162D03F3230BBDE157
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'h736A8FFB5960517D1D3F81758E675FF95FB76F97C3873BEE73D85F14C63305F0
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h08003A5164A595E7215DCC86DAF85431,
    256'hC51478DFB6FD8B9716F318A25E86D016A3CE59685EEBCEC5A236504519CD208C
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h5418C9C50A7DC6774276BB36DBE9D5F1,
    256'h6016D36BE73F17BD56D2AC51FB640552FE65C0443EFB554C972639F56AD18D26
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h987D63F44D9B0998AAD73CBD0A318B80
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'hF7A0D62394CFA969020470FD96E8908B
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'h42A82C0A
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h0AEC3AC667A1B8DC4B6A783FD75D994093A813C5
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h488639840C191959
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'hC5E4E3A6F7A5C571D515EA8B53E1DA6C
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h31233617
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'h91FC063936BF31459A7B4284DF948387741AC5F9
  };

  // Default icache scrambling key
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstRvCoreIbexIbexKeyDefault = {
    128'hAD2C6FE996DF13C6C70A43FE9364B0B8
  };

  // Default icache scrambling nonce
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstRvCoreIbexIbexNonceDefault = {
    64'hF85DBDFF5FB5520D
  };

endpackage : top_earlgrey_rnd_cnst_pkg
