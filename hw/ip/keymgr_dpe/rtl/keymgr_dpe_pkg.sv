// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package keymgr_dpe_pkg;

  // Most of the parameters are directly reused from keymgr_pkg
  import keymgr_pkg::*;

  parameter int DpeNumBootStages = 4;  // Number of key manager stages
  parameter int DpeNumSlots = 4;
  parameter int DpeNumSlotsWidth = prim_util_pkg::vbits(DpeNumSlots);
  parameter int DpeNumBootStagesWidth = $clog2(DpeNumBootStages);


  typedef logic [DpeNumSlotsWidth-1:0] keymgr_dpe_slot_idx_e;

  // Enumeration for operation
  typedef enum logic [2:0] {
    OpDpeAdvance = 0,
    OpDpeErase = 1,
    OpDpeGenSwOut = 2,
    OpDpeGenHwOut = 3,
    OpDpeDisable = 4
  } keymgr_dpe_ops_e;

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 8 -n 10 \
  //      -s 4101887575 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (50.00%)
  //  6: |||||||||||||| (35.71%)
  //  7: || (7.14%)
  //  8: || (7.14%)
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 8
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 8
  //
  localparam int StateWidth = 10;
  typedef enum logic [StateWidth-1:0] {
    StCtrlDpeReset          = 10'b1001010101,
    StCtrlDpeEntropyReseed  = 10'b0100000100,
    StCtrlDpeRandom         = 10'b0010110011,
    StCtrlDpeRootKey        = 10'b1111110110,
    StCtrlDpeAvailable      = 10'b0111101000,
    StCtrlDpeWipe           = 10'b0001001011,
    StCtrlDpeInvalid        = 10'b1100111001,
    StCtrlDpeDisabled       = 10'b1010001110
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
    logic allow_child;
    logic exportable;
    logic retain_parent;
  } keymgr_dpe_policy_t;

  // An internal secret key slot
  typedef struct packed {
    logic valid;
    logic [DpeNumBootStagesWidth-1:0] boot_stage;
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
    SlotWipeAll
  } keymgr_dpe_key_update_e;

  localparam keymgr_dpe_policy_t DEFAULT_UDS_POLICY = '{
    allow_child   : 1'b1,
    exportable    : 1'b0,
    retain_parent : 1'b0
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
