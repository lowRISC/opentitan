// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package keymgr_dpe_pkg;

  // Most of the parameters are directly reused from keymgr_pkg
  import keymgr_pkg::*;

  parameter int DpeNumSlots = 8;
  parameter int DpeNumSlotsWidth = prim_util_pkg::vbits(DpeNumSlots);

  // Chip Device ID
  parameter int DeviceIdWidth = 256;
  typedef logic [DeviceIdWidth-1:0] keymgr_dpe_device_id_t;

  // keymgr and keymgr_dpe have different maximum KMAC input widths. The below widths correspond to
  // the following inputs to advance to the creator root key state:
  //   - Software binding
  //   - Revision seed
  //   - OTP device ID
  //   - LC keymgr diversification value
  //   - ROM digests
  //   - Creator seed
  parameter int DpeAdvDataWidth = SwBindingWidth + KeyWidth + DeviceIdWidth +
      lc_ctrl_pkg::LcKeymgrDivWidth + KeyWidth*keymgr_dpe_reg_pkg::NumRomDigestInputs + KeyWidth;

  typedef logic [DpeNumSlotsWidth-1:0] keymgr_dpe_slot_idx_e;

  // Enumeration for operation
  typedef enum logic [2:0] {
    OpDpeAdvance = 0,
    OpDpeErase = 1,
    OpDpeGenSwOut = 2,
    OpDpeGenHwOut = 3,
    OpDpeDisable = 4,
    OpDpeLoadRootKey = 5
  } keymgr_dpe_ops_e;

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

  // TODO(#354): Define further policy bits and extend this struct
  typedef struct packed {
    logic retain_parent;
    logic exportable;
    logic allow_child;
  } keymgr_dpe_policy_t;

  // Parameter Key Width
  parameter int KeyMgrKeyWidth = 256;

  // Input struct for secrets required by the keymgr dpe.
  typedef struct packed {
    logic [KeyMgrKeyWidth-1:0]  share0;
    logic                       share0_valid;
    logic [KeyMgrKeyWidth-1:0]  share1;
    logic                       share1_valid;
  } keymgr_dpe_creator_root_key_t;

  typedef struct packed {
    logic [KeyMgrKeyWidth-1:0]  seed;
    logic                       seed_valid;
  } keymgr_dpe_creator_seed_t;

  typedef struct packed {
    logic [KeyMgrKeyWidth-1:0]  seed;
    logic                       seed_valid;
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

  // Enumeration for boot stage. In the BootStageRuntime stage, there is no limit on the number of
  // advance calls.
  parameter int DpeBootStagesWidth = 2;
  typedef enum logic [DpeBootStagesWidth-1:0] {
    BootStageCreator = 0,
    BootStageOwner   = 1,
    BootStageRuntime = 2
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

  localparam keymgr_dpe_policy_t DEFAULT_UDS_POLICY = '{
    retain_parent : 1'b0,
    exportable    : 1'b0,
    allow_child   : 1'b1
  };

  // Keymgr_dpe requires more lc_en copies than keymgr
  typedef enum logic [2:0] {
    KeymgrDpeEnCtrl,
    KeymgrDpeEnCfg,
    KeymgrDpeEnBinding,
    KeymgrDpeEnDebug,
    KeymgrDpeEnLast
  } keymgr_lc_en_usage_e;

endpackage : keymgr_dpe_pkg
