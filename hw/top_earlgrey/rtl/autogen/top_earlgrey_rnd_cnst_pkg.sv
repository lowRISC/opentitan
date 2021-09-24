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

  ////////////////////////////////////////////
  // lc_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivInvalid = {
    128'hFDB92558E2D9C5D24440722325A93144
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivTestDevRma = {
    128'h6FAF88F22BCCD612D1C09F5C02B2C8D1
  };

  // Compile-time random bits for lc state group diversification value
  parameter lc_ctrl_pkg::lc_keymgr_div_t RndCnstLcCtrlLcKeymgrDivProduction = {
    128'h79EE911CE801484BA8373086F9DD4EEE
  };

  ////////////////////////////////////////////
  // alert_handler
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter alert_pkg::lfsr_seed_t RndCnstAlertHandlerLfsrSeed = {
    32'h7B93136F
  };

  // Compile-time random permutation for LFSR output
  parameter alert_pkg::lfsr_perm_t RndCnstAlertHandlerLfsrPerm = {
    160'hAF33379628B29DF3261A1E1BE933AB38A840EEE0
  };

  ////////////////////////////////////////////
  // sram_ctrl_ret_aon
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlRetAonSramKey = {
    128'h0738F30D9006289A1D7D9D0CE1DD7D7C
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlRetAonSramNonce = {
    128'hFE8F673FBA39BB679D58AA91AEB2691C
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlRetAonLfsrSeed = {
    32'hAE24AF11
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlRetAonLfsrPerm = {
    160'h25DA5869DC96FE354F1DA55E9123CB082C63B331
  };

  ////////////////////////////////////////////
  // flash_ctrl
  ////////////////////////////////////////////
  // Compile-time random bits for default address key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlAddrKey = {
    128'h369AE283EEC5E43D4B16446726A27B8F
  };

  // Compile-time random bits for default data key
  parameter flash_ctrl_pkg::flash_key_t RndCnstFlashCtrlDataKey = {
    128'h1A07EB42A37DBFB7BE9BB6E69A7D3C5F
  };

  // Compile-time random bits for initial LFSR seed
  parameter flash_ctrl_pkg::lfsr_seed_t RndCnstFlashCtrlLfsrSeed = {
    32'h096F534D
  };

  // Compile-time random permutation for LFSR output
  parameter flash_ctrl_pkg::lfsr_perm_t RndCnstFlashCtrlLfsrPerm = {
    160'hC0FB0F38E6BD6744364B005EC493761479F5173A
  };

  ////////////////////////////////////////////
  // aes
  ////////////////////////////////////////////
  // Default seed of the PRNG used for register clearing.
  parameter aes_pkg::clearing_lfsr_seed_t RndCnstAesClearingLfsrSeed = {
    64'hED204633871CB178
  };

  // Permutation applied to the LFSR of the PRNG used for clearing.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingLfsrPerm = {
    128'h99B01E35560F2EB97E3047685D6B7BD8,
    256'h7B029229DA078DF923F7D0F46154C34BA9D43C734AF2A1EAA8E0F3270944E4D9
  };

  // Permutation applied to the clearing PRNG output for clearing the second share of registers.
  parameter aes_pkg::clearing_lfsr_perm_t RndCnstAesClearingSharePerm = {
    128'h7D9CF783C36C02E6CBD0C89A7299BAC2,
    256'h45B9FB80C85367BB5E53C511341509877FB72286F4E9E3047871A354AFAD126A
  };

  // Default seed of the PRNG used for masking.
  parameter aes_pkg::masking_lfsr_seed_t RndCnstAesMaskingLfsrSeed = {
    160'hD6E49C544BA9DCDFF0245E84D6F5F03ECAEF7217
  };

  // Permutation applied to the LFSR chunks of the PRNG used for masking.
  parameter aes_pkg::mskg_chunk_lfsr_perm_t RndCnstAesMskgChunkLfsrPerm = {
    160'h46FA4BD6DC82BEB0A4E30305AA371E9C64E2BF26
  };

  ////////////////////////////////////////////
  // kmac
  ////////////////////////////////////////////
  // Compile-time random permutation for LFSR output
  parameter kmac_pkg::lfsr_perm_t RndCnstKmacLfsrPerm = {
    128'h6A2FF34254A73BC530784BB425DBC3E6,
    256'h41F24F8B356F7AF1AADED15CA6567E0FA81803E317663A98B308F4D042A5585C
  };

  ////////////////////////////////////////////
  // otbn
  ////////////////////////////////////////////
  // Default seed of the PRNG used for URND.
  parameter otbn_pkg::urnd_lfsr_seed_t RndCnstOtbnUrndLfsrSeed = {
    256'hF9E20B072B46413FEA8F46C61A39EBB93E4EF606D8CEFA03D0EC61B1BDCBC0E3
  };

  // Permutation applied to the LFSR chunks of the PRNG used for URND.
  parameter otbn_pkg::urnd_chunk_lfsr_perm_t RndCnstOtbnUrndChunkLfsrPerm = {
    128'hE25A640354EA467D232E123F0F1B7D55,
    256'hB822406C1AC8264F252726BC578C518F2C2BE06B38DED6EB7D84A1FCC75EEE5D
  };

  // Compile-time random reset value for IMem/DMem scrambling key.
  parameter otp_ctrl_pkg::otbn_key_t RndCnstOtbnOtbnKey = {
    128'h4F5A0A911C1BCAFE7663F6D1FBE7E440
  };

  // Compile-time random reset value for IMem/DMem scrambling nonce.
  parameter otp_ctrl_pkg::otbn_nonce_t RndCnstOtbnOtbnNonce = {
    64'h034816103A781D0A
  };

  ////////////////////////////////////////////
  // keymgr
  ////////////////////////////////////////////
  // Compile-time random bits for initial LFSR seed
  parameter keymgr_pkg::lfsr_seed_t RndCnstKeymgrLfsrSeed = {
    64'h2761603352213B7A
  };

  // Compile-time random permutation for LFSR output
  parameter keymgr_pkg::lfsr_perm_t RndCnstKeymgrLfsrPerm = {
    128'h430A9EBCD7DA3FFDA144CA00831DD90E,
    256'h7E476CAEBD513CFB8A6D46138F9294EBADF24097556274B1D718CA3AC8A412C5
  };

  // Compile-time random permutation for entropy used in share overriding
  parameter keymgr_pkg::rand_perm_t RndCnstKeymgrRandPerm = {
    160'hAE95D648FE096166A7E2C81EE22EF834C71E6E88
  };

  // Compile-time random bits for revision seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrRevisionSeed = {
    256'h17A9838DD4CD7F1BDCE673B937A6D75202FEDBF893BF7D52C8A744AD83D2630B
  };

  // Compile-time random bits for creator identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrCreatorIdentitySeed = {
    256'hC20C05A20251023541544776930BE76BFBB22E1D8AAA4783F2B5E094E3E8D3F8
  };

  // Compile-time random bits for owner intermediate identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIntIdentitySeed = {
    256'h93CDB1D9A6A60050EF0D8A166D91200DC6757907237DF4401908799DFA1FE8F2
  };

  // Compile-time random bits for owner identity seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrOwnerIdentitySeed = {
    256'hA88601CA1695A7C8C5D32486AAC4E086628D6C8CA138F65D25DFA5F9C912F354
  };

  // Compile-time random bits for software generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrSoftOutputSeed = {
    256'hDF273097A573A411332EFD86009BD0A175F08814ECC17AB02CC1E3404E1CD8BF
  };

  // Compile-time random bits for hardware generation seed
  parameter keymgr_pkg::seed_t RndCnstKeymgrHardOutputSeed = {
    256'h69582E71443C8BE0FC00DE9D9734C3FE7F4266D10A752DE74814F2A3079F69A3
  };

  // Compile-time random bits for generation seed when aes destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrAesSeed = {
    256'h73E5BC251B143B74476E576754125D61930D203F199A87C123C074E020FD5028
  };

  // Compile-time random bits for generation seed when kmac destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrKmacSeed = {
    256'hCE44CBFF5E09E6DD3AE54E9E45DA6E662FB69C3AAB936B415A0D6E7185EAA2E0
  };

  // Compile-time random bits for generation seed when otbn destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrOtbnSeed = {
    256'hFCC581B66AE11D33F678E7D227881BCFE58A331208F189DE6265EDC8FDE06DB0
  };

  // Compile-time random bits for generation seed when no destination selected
  parameter keymgr_pkg::seed_t RndCnstKeymgrNoneSeed = {
    256'hB76A8AFF9E4DA0E3FF9F3036FD9C13AC08496DB56FBC4894D38BD8674F4B542D
  };

  ////////////////////////////////////////////
  // csrng
  ////////////////////////////////////////////
  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivNonProduction = {
    128'h4093F0EC256B2646079C10F2F41F73AF,
    256'h3FC6AFBEC695054A0407221FB798AB7845C3FEAB0D2F4C7CF730A5675D7717A4
  };

  // Compile-time random bits for csrng state group diversification value
  parameter csrng_pkg::cs_keymgr_div_t RndCnstCsrngCsKeymgrDivProduction = {
    128'h1F44B085A363CB599DF4DE1E830F9365,
    256'h8A789BDC189F345CF4E341F211C9D00BEEFA4D4C2E269435471A7A682A6260EB
  };

  ////////////////////////////////////////////
  // sram_ctrl_main
  ////////////////////////////////////////////
  // Compile-time random reset value for SRAM scrambling key.
  parameter otp_ctrl_pkg::sram_key_t RndCnstSramCtrlMainSramKey = {
    128'h37F67765A0D2EB0CB514E4199CF3DE67
  };

  // Compile-time random reset value for SRAM scrambling nonce.
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramCtrlMainSramNonce = {
    128'h0C9E673E4DB3FEE8922D1F0BCDD09153
  };

  // Compile-time random bits for initial LFSR seed
  parameter sram_ctrl_pkg::lfsr_seed_t RndCnstSramCtrlMainLfsrSeed = {
    32'hF45740EB
  };

  // Compile-time random permutation for LFSR output
  parameter sram_ctrl_pkg::lfsr_perm_t RndCnstSramCtrlMainLfsrPerm = {
    160'h8DFE6EBD18CD97C1A58A179D524A9A3EE0D004B3
  };

  ////////////////////////////////////////////
  // rom_ctrl
  ////////////////////////////////////////////
  // Fixed nonce used for address / data scrambling
  parameter bit [63:0] RndCnstRomCtrlScrNonce = {
    64'h0EBAD9424AE5E2CF
  };

  // Randomised constant used as a scrambling key for ROM data
  parameter bit [127:0] RndCnstRomCtrlScrKey = {
    128'h1893C0CE9E8E5600260058176D17F366
  };

  ////////////////////////////////////////////
  // rv_core_ibex
  ////////////////////////////////////////////
  // Default seed of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_seed_t RndCnstRvCoreIbexLfsrSeed = {
    32'h7B99DCC9
  };

  // Permutation applied to the LFSR of the PRNG used for random instructions.
  parameter ibex_pkg::lfsr_perm_t RndCnstRvCoreIbexLfsrPerm = {
    160'hB3918EB0D96C66B3D0572F8322007C4EFEF86955
  };

endpackage : top_earlgrey_rnd_cnst_pkg
