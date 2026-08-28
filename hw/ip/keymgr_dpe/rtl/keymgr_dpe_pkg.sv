// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Keymgr_dpe Package
//

package keymgr_dpe_pkg;

  ///////////////////////////////////////
  // Keymgr_dpe: parameters & typedefs //
  ///////////////////////////////////////

  // Chip Device ID
  parameter int DeviceIdWidth         = 256;
  typedef logic [DeviceIdWidth-1:0]   keymgr_dpe_device_id_t;
  // Width and number of shares for the keymgr_dpe key
  parameter int KeyWidth              = 256;
  parameter int Shares                = 2;
  // Key version length
  parameter int KeyVersionWidth       = 32;
  // Width of wide sideload key (consumed by OTBN)
  parameter int WideHwKeyWidth        = 512;
  // Data width of KMAC interface
  parameter int KmacDataIfWidth       = 64;
  // Width of SW binding value
  parameter int SwBindingWidth        = 32 * keymgr_dpe_reg_pkg::NumSwBindingReg;
  // Width calculations
  // These are the largest calculations in use across all stages
  parameter int IdDataWidth           = KeyWidth;
  // key version + salt + key ID + constant
  parameter int GenDataWidth          = 32 + 32 * keymgr_dpe_reg_pkg::NumSaltReg + KeyWidth*2;
  // Max Payload Width to derivation function
  // see security strength description https://keccak.team/keccak.html
  // The max width here is chosen arbitrarily to ensure we do not get out of hand.
  // Since KMAC is a MAC operation, the data can be as long as we need.
  parameter int KDFMaxWidth           = 1984;


  /////////////////////////////////////
  // Keymgr_dpe: Operations & Policy //
  /////////////////////////////////////

  // Enumeration for operation
  typedef enum logic [2:0] {
    OpDpeAdvance     = 0,
    OpDpeErase       = 1,
    OpDpeGenSwOut    = 2,
    OpDpeGenHwOut    = 3,
    OpDpeDisable     = 4,
    OpDpeLoadRootKey = 5
  } keymgr_dpe_ops_e;

  // Enumeration for operation status
  typedef enum logic [1:0] {
    OpIdle        = 0,
    OpWip         = 1,
    OpDoneSuccess = 2,
    OpDoneFail    = 3
  } keymgr_dpe_op_status_e;

  // TODO(#354): Define further policy bits and extend this struct
  typedef struct packed {
    logic retain_parent;
    logic exportable;
    logic allow_child;
  } keymgr_dpe_policy_t;

  localparam keymgr_dpe_policy_t DEFAULT_UDS_POLICY = '{
    retain_parent : 1'b0,
    exportable    : 1'b0,
    allow_child   : 1'b1
  };


  /////////////////////
  // Keymgr_dpe: FSM //
  /////////////////////

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 9 -n 10 \
  //      -s 3359281180 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (52.78%)
  //  6: ||||||||||||||| (41.67%)
  //  7: | (2.78%)
  //  8: | (2.78%)
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 8
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 8
  //
  localparam int StateWidth = 10;
  typedef enum logic [StateWidth-1:0] {
    StCtrlDpeReset         = 10'b1000011111,
    StCtrlDpeEntropyReseed = 10'b1111000011,
    StCtrlDpeRandom        = 10'b0001110010,
    StCtrlDpeRootKey       = 10'b0110101010,
    StCtrlDpeAvailable     = 10'b0111111101,
    StCtrlDpeWipe          = 10'b0001000101,
    StCtrlDpeDisabling     = 10'b1010110001,
    StCtrlDpeDisabled      = 10'b1100100100,
    StCtrlDpeInvalid       = 10'b1101011000
  } keymgr_dpe_working_state_e;

  // Enumeration for working state exposed to software
  typedef enum logic [1:0] {
    StWorkDpeReset = 0,
    StWorkDpeAvailable,
    StWorkDpeDisabled,
    StWorkDpeInvalid
  } keymgr_dpe_exposed_working_state_e;


  /////////////////////////////////////////////
  // Keymgr_dpe: Default Lfsr configurations //
  /////////////////////////////////////////////

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


  ///////////////////////////////
  // Keymgr_dpe: Default Seeds //
  ///////////////////////////////

  // These have been generated with the following command by incrementing the --seed argument
  // for every seed.
  // util/design/gen-lfsr-seed.py --width 256 --seed 7535190 --prefix ""
  typedef logic [KeyWidth-1:0] seed_t;
  parameter seed_t RndCnstRevisionSeedDefault =
    256'h69802e51_bacf8874_e650d692_e3d8a646_2d3f158f_0bf7961d_d346f880_b4d52170;
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


  //////////////////////////////////////
  // Keymgr_dpe: Secret & Seed Inputs //
  //////////////////////////////////////

  // Input struct for secrets required by the keymgr dpe.
  typedef struct packed {
    logic [KeyWidth-1:0]  share0;
    logic                 share0_valid;
    logic [KeyWidth-1:0]  share1;
    logic                 share1_valid;
  } keymgr_dpe_creator_root_key_t;

  typedef struct packed {
    logic [KeyWidth-1:0]  seed;
    logic                 seed_valid;
  } keymgr_dpe_creator_seed_t;

  typedef struct packed {
    logic [KeyWidth-1:0]  seed;
    logic                 seed_valid;
  } keymgr_dpe_owner_seed_t;

  parameter keymgr_dpe_creator_root_key_t KEYMGR_DPE_CREATOR_ROOT_KEY_DEFAULT = '{
    share0       : 256'hefb7ea7ee90093cf4affd9aaa2d6c0ec446cfdf5f2d5a0bfd7e2d93edc63a102,
    share0_valid : 1'b1,
    share1       : 256'h56d24a00181de99e0f690b447a8dde2a1ffb8bc306707107aa6e2410f15cfc37,
    share1_valid : 1'b1
  };

  parameter keymgr_dpe_creator_seed_t KEYMGR_DPE_CREATOR_SEED_DEFAULT = '{
    seed         : 256'hc7c50b38655cc87f821e5b07fed85d2c07e222a9e00bef308b3eccba0ba406fa,
    seed_valid   : 1'b1
  };

  parameter keymgr_dpe_owner_seed_t KEYMGR_DPE_OWNER_SEED_DEFAULT = '{
    seed         : 256'hf5052c0f14782d8b066be9f49c0b2000d3643ff3723ea7db972f69cd3e2e3e68,
    seed_valid   : 1'b1
  };


  /////////////////////////////////
  // Keymgr_dpe: Key Connections //
  /////////////////////////////////

  // Key connection to various symmetric modules
  typedef struct packed {
    logic valid;
    logic [Shares-1:0][KeyWidth-1:0] key;
  } hw_key_req_t;

  // Key connection to otbn
  typedef struct packed {
    logic valid;
    logic [Shares-1:0][WideHwKeyWidth-1:0] key;
  } wide_hw_key_req_t;

  parameter hw_key_req_t HW_KEY_REQ_DEFAULT = '{
    valid : 1'b0,
    key   : {Shares{KeyWidth'(32'hDEADBEEF)}}
  };

  parameter wide_hw_key_req_t WIDE_HW_KEY_REQ_DEFAULT = '{
    valid : 1'b0,
    key   : {Shares{WideHwKeyWidth'(32'hDEADBEEF)}}
  };


  ///////////////////////////////////////
  // Keymgr_dpe: Boot Stage & Key Slot //
  ///////////////////////////////////////

  // Enumeration for boot stage. In the BootStageRuntime stage, there is no limit on the number of
  // advance calls.
  parameter int DpeBootStagesWidth = 2;
  typedef enum logic [DpeBootStagesWidth-1:0] {
    BootStageCreator  = 0,
    BootStageOwnerInt = 1,
    BootStageOwner    = 2,
    BootStageRuntime  = 3
  } keymgr_dpe_boot_stage_e;

  // An internal secret key slot
  typedef struct packed {
    logic valid;
    keymgr_dpe_boot_stage_e boot_stage;
    logic [Shares-1:0][KeyWidth-1:0] key;
    logic [KeyVersionWidth-1:0] max_key_version;
    keymgr_dpe_policy_t key_policy;
  } keymgr_dpe_slot_t;

  typedef enum logic [2:0] {
    SlotUpdateIdle,
    SlotDestRandomize,
    SlotLoadRoot,
    SlotLoadFromKmac,
    SlotErase,
    SlotWipeInternalOnly,
    SlotWipeAll
  } keymgr_dpe_key_update_e;


  /////////////////////////////////////////
  // Keymgr_dpe: Life Cycle Enable Usage //
  /////////////////////////////////////////

  // Keymgr_dpe requires more lc_en copies than keymgr
  typedef enum logic [2:0] {
    KeymgrDpeEnCtrl,
    KeymgrDpeEnCfg,
    KeymgrDpeEnBinding,
    KeymgrDpeEnDebug,
    KeymgrDpeEnLast
  } keymgr_dpe_lc_en_usage_e;


  //////////////////////////
  // Keymgr_dpe: Sideload //
  //////////////////////////

  // Enumeration for sideload sel
  typedef enum logic [1:0] {
    None,
    Aes,
    Kmac,
    Otbn
  } keymgr_dpe_key_dest_e;

  // Enumeration for actual key slot idx
  typedef enum logic [1:0] {
    AesIdx,
    KmacIdx,
    OtbnIdx,
    LastIdx
  } keymgr_dpe_sideload_slot_idx_e;

  typedef enum logic [2:0] {
    SideLoadClrIdle,
    SideLoadClrAes,
    SideLoadClrKmac,
    SideLoadClrOtbn
  } keymgr_dpe_sideload_clr_e;


  /////////////////////////////////
  // Keymgr_dpe: Errors & Faults //
  /////////////////////////////////

  // keymgr_dpe has 4 categories of errors
  // sync errors  - recoverable errors that happen during keymgr_dpe operation
  // async errors - recoverable errors that happen asynchronously
  // sync faults  - fatal errors that happen during keymgr_dpe operation
  // async faults - fatal errors that happen asynchronously

  typedef enum logic [1:0] {
    SyncErrInvalidOp,
    SyncErrInvalidIn,
    SyncErrLastIdx
  } keymgr_dpe_sync_error_e;

  typedef enum logic [1:0] {
    AsyncErrShadowUpdate,
    AsyncErrLastIdx
  } keymgr_dpe_async_error_e;

  typedef enum logic [1:0] {
    SyncFaultKmacOp,
    SyncFaultKmacOut,
    SyncFaultSideSel,
    SyncFaultLastIdx
  } keymgr_dpe_sync_fault_e;

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
  } keymgr_dpe_async_fault_e;

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
  } keymgr_dpe_fault_pos_e;

  // Bit position of error code
  // Error is encoded as 1 error per bit
  typedef enum logic [2:0] {
    ErrInvalidOp,
    ErrInvalidIn,
    ErrShadowUpdate,
    ErrLastPos
  } keymgr_dpe_err_pos_e;


  ///////////////////////////
  // Keymgr_dpe: Functions //
  ///////////////////////////

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

endpackage : keymgr_dpe_pkg
