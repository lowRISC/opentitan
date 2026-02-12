// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// key manager package
//

package keymgr_pkg;

  parameter int KeyWidth = 256;
  parameter int CDIs = 2; // 2 different CDIs, sealing / attestation
  parameter int CdiWidth = prim_util_pkg::vbits(CDIs);
  parameter int OtbnKeyWidth = 384;
  parameter int DigestWidth = 128;     // uses truncated hash
  parameter int KmacDataIfWidth = 64;  // KMAC interface data width
  parameter int KeyMgrStages = 3; // Number of key manager stages (creator, ownerInt, owner)
  parameter int SwBindingWidth = 32 * keymgr_reg_pkg::NumSwBindingReg;
  parameter int SaltWidth = 32 * keymgr_reg_pkg::NumSaltReg;
  parameter int Shares = 2; // number of key shares
  parameter int EdnWidth = edn_pkg::ENDPOINT_BUS_WIDTH;
  parameter int KeyVersionWidth = 32;  // Key version length for individual DICE stage

  // These should be defined in another module's package
  parameter int HealthStateWidth = 128;
  parameter int DevIdWidth = 256;
  parameter int MaxWidth = 256;

  // Default seeds
  // These have been generated with the following command by incrementing the --seed argument
  // for every seed.
  // util/design/gen-lfsr-seed.py --width 256 --seed 7535190 --prefix ""
  typedef logic [KeyWidth-1:0] seed_t;
  parameter seed_t RndCnstRevisionSeedDefault =
    256'h69802e51_bacf8874_e650d692_e3d8a646_2d3f158f_0bf7961d_d346f880_b4d52170;
  parameter seed_t RndCnstCreatorIdentitySeedDefault =
    256'h344bff84_d3edf83e_aa565c5e_6c2d22f2_75283734_15cf6d83_32cd3752_731817c;
  parameter seed_t RndCnstOwnerIntIdentitySeedDefault =
    256'h32a37bf9_2627382b_47180548_1fc4b847_a7eba1ce_c13e80ab_030f847e_9bd902e;
  parameter seed_t RndCnstOwnerIdentitySeedDefault =
    256'hc1ba416c_822ad676_e4f54f36_33d8dc7e_00ccfb8b_92209f1b_d3229348_275ebda;
  parameter seed_t RndCnstSoftOutputSeedDefault =
    256'h23cbe85e_62e39992_4ab8d6a6_acbf12f0_0ca6f488_63eaa428_ffb11b26_c5282b14;
  parameter seed_t RndCnstHardOutputSeedDefault =
    256'h877ef0b9_aceaefc5_693b1aa7_e43a7f3d_ee7d63b6_4e73e182_b49cbf87_2872f2c;

  // Target based deriviation seeds
  // These are used during the generation stages for sideload
  parameter seed_t RndCnstNoneSeedDefault =
    256'h6013ba4d_8d04fe4f_80cb0472_536c9679_08b82f1d_98a4e405_cb4680ec_3a4a8d7a;
  parameter seed_t RndCnstAesSeedDefault =
    256'he16a8fa9_5b613cd5_fb9ad23f_bd8347e1_64e45dac_5d08a41b_e83caa37_e03d9482;
  parameter seed_t RndCnstKmacSeedDefault =
    256'hc57f4c0b_b308e83f_3fc4bc63_d87dd67d_9071dc1c_e19484c8_3c94fb97_dd634369;
  parameter seed_t RndCnstOtbnSeedDefault =
    256'hcbcb4d2d_0abeb81b_ca7451ae_d1e2479d_ba13530a_d046b945_646aa127_bd4f6a38;
  parameter seed_t RndCnstCdiDefault =
    256'h54180905_d14c1d2f_2dda1522_f332bc0e_fcd6b92f_f0f9db75_3a9a9544_26a42eab;

  // Default Lfsr configurations
  // These LFSR parameters have been generated with
  // $ util/design/gen-lfsr-seed.py --width 64 --seed 691876113 --prefix ""
  parameter int LfsrWidth = 64;
  typedef logic [LfsrWidth-1:0] lfsr_seed_t;
  typedef logic [LfsrWidth-1:0][$clog2(LfsrWidth)-1:0] lfsr_perm_t;
  parameter lfsr_seed_t RndCnstLfsrSeedDefault = 64'h22d326255bd24320;
  parameter lfsr_perm_t RndCnstLfsrPermDefault = {
    128'h16108c9f9008aa37e5118d1ec1df64a7,
    256'h24f3f1b73537f42d38383ee8f897286df81d49ab54b6bbbb666cbd1a16c41252
  };

  // Random permutation
  parameter int RandWidth = LfsrWidth / 2;
  typedef logic [RandWidth-1:0][$clog2(RandWidth)-1:0] rand_perm_t;
  parameter rand_perm_t RndCnstRandPermDefault = {
    160'h62089181d2a6be2ce145e2e27099ededbd7dceb0
  };

  // Width calculations
  // These are the largest calculations in use across all stages
  parameter int AdvDataWidth = SwBindingWidth + 2*KeyWidth + DevIdWidth + HealthStateWidth;
  parameter int IdDataWidth = KeyWidth;
  // key version + salt + key ID + constant
  parameter int GenDataWidth = 32 + SaltWidth + KeyWidth*2;
  parameter int StageWidth = $clog2(KeyMgrStages);
  // Max Payload Width to derivation function
  // see security strength description https://keccak.team/keccak.html
  // The max width here is chosen arbitrarily to ensure we do not get out of hand.
  // Since KMAC is a MAC operation, the data can be as long as we need.
  parameter int KDFMaxWidth = 1984;

  // Enumeration for operations
  typedef enum logic [1:0] {
    Creator,
    OwnerInt,
    Owner,
    Disable
  } keymgr_stage_e;

  // Enumeration for sideload sel
  typedef enum logic [1:0] {
    None,
    Aes,
    Kmac,
    Otbn
  } keymgr_key_dest_e;

  // Enumeration for actual key slot idx
  typedef enum logic [1:0] {
    AesIdx,
    KmacIdx,
    OtbnIdx,
    LastIdx
  } keymgr_sideload_slot_idx_e;

  // Enumeration for key select
  typedef enum logic {
    HwKey = 0,
    SwKey = 1
  } keymgr_gen_out_e;

  // Enumeration for operation
  typedef enum logic [2:0] {
    OpAdvance = 0,
    OpGenId = 1,
    OpGenSwOut = 2,
    OpGenHwOut = 3,
    OpDisable = 4
  } keymgr_ops_e;

  // Enumeration for working state exposed to software
  typedef enum logic [2:0] {
    StReset,
    StInit,
    StCreatorRootKey,
    StOwnerIntKey,
    StOwnerKey,
    StDisabled,
    StInvalid
  } keymgr_working_state_e;

  // Enumeration for operation status
  typedef enum logic [1:0] {
    OpIdle = 0,
    OpWip = 1,
    OpDoneSuccess = 2,
    OpDoneFail = 3
  } keymgr_op_status_e;

  // keymgr has 4 categories of errors
  // sync errors  - recoverable errors that happen during keymgr operation
  // async errors - recoverable errors that happen asynchronously
  // sync faults  - fatal errors that happen during keymgr operation
  // async faults - fatal errors that happen asynchronously

  typedef enum logic [1:0] {
    SyncErrInvalidOp,
    SyncErrInvalidIn,
    SyncErrLastIdx
  } keymgr_sync_error_e;

  typedef enum logic [1:0] {
    AsyncErrShadowUpdate,
    AsyncErrLastIdx
  } keymgr_async_error_e;

  typedef enum logic [1:0] {
    SyncFaultKmacOp,
    SyncFaultKmacOut,
    SyncFaultSideSel,
    SyncFaultLastIdx
  } keymgr_sync_fault_e;

  typedef enum logic [3:0] {
    AsyncFaultKmacCmd,
    AsyncFaultKmacFsm,
    AsyncFaultKmacDone,
    AsyncFaultRegIntg,
    AsyncFaultShadow,
    AsyncFaultFsmIntg,
    AsyncFaultFsmChk,
    AsyncFaultCntErr,
    AsyncFaultRCntErr,
    AsyncFaultSideErr,
    AsyncFaultKeyEcc,
    AsyncFaultLastIdx
  } keymgr_async_fault_e;


  // Bit position of error code
  // Error is encoded as 1 error per bit
  typedef enum logic [2:0] {
    ErrInvalidOp,
    ErrInvalidIn,
    ErrShadowUpdate,
    ErrLastPos
  } keymgr_err_pos_e;

  // Bit position of fault status
  typedef enum logic [3:0] {
    FaultKmacCmd,
    FaultKmacFsm,
    FaultKmacDone,
    FaultKmacOp,
    FaultKmacOut,
    FaultRegIntg,
    FaultShadow,
    FaultCtrlFsm,
    FaultCtrlFsmChk,
    FaultCtrlCnt,
    FaultReseedCnt,
    FaultSideFsm,
    FaultSideSel,
    FaultKeyEcc,
    FaultLastPos
  } keymgr_fault_pos_e;

  typedef enum logic [2:0] {
    KeyUpdateIdle,
    KeyUpdateRandom,
    KeyUpdateRoot,
    KeyUpdateKmac,
    KeyUpdateWipe
  } keymgr_key_update_e;

  typedef enum logic [2:0] {
    SideLoadClrIdle,
    SideLoadClrAes,
    SideLoadClrKmac,
    SideLoadClrOtbn
  } keymgr_sideload_clr_e;

  // Key connection to various symmetric modules
  typedef struct packed {
    logic valid;
    logic [Shares-1:0][KeyWidth-1:0] key;
  } hw_key_req_t;

  // Key connection to otbn
  typedef struct packed {
    logic valid;
    logic [Shares-1:0][OtbnKeyWidth-1:0] key;
  } otbn_key_req_t;

  parameter hw_key_req_t HW_KEY_REQ_DEFAULT = '{
    valid: 1'b0,
    key: {Shares{KeyWidth'(32'hDEADBEEF)}}
  };

  parameter otbn_key_req_t OTBN_KEY_REQ_DEFAULT = '{
    valid: 1'b0,
    key: {Shares{OtbnKeyWidth'(32'hDEADBEEF)}}
  };

  // The following structs should be sourced from other modules
  // defined here temporarily

  // lc keymgr enable usage
  typedef enum logic [1:0] {
    KeyMgrEnCtrl,
    KeyMgrEnCfgEn,
    KeyMgrEnSwBindingEn,
    KeyMgrEnLast
  } keymgr_lc_en_usage_e;

  // perm_data
  function automatic logic[RandWidth-1:0] perm_data (logic [RandWidth-1:0] data,
    rand_perm_t perm_sel);

    for (int k = 0; k < 32; k++) begin : gen_data_loop
      perm_data[k] = data[perm_sel[k]];
    end

  endfunction

  // checks for all 0's or all 1's of value
  function automatic logic valid_data_chk (logic [KeyWidth-1:0] value);
    return |value & ~&value;
  endfunction

endpackage : keymgr_pkg
