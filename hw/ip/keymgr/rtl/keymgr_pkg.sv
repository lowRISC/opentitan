// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// key manager package
//

package keymgr_pkg;

  localparam int KeyWidth = 256;
  localparam int DigestWidth = 128;  // uses truncated hash
  localparam int KmacDataIfWidth = 64; // KMAC interface data width
  localparam int KeyMgrStages = 3;   // Number of key manager stages (creator, ownerInt, owner)
  localparam int RomExtDescWidth = 128; // Size of rom_ext hash, truncated
  localparam int LfsrWidth = 64;
  localparam int Shares = 2; // number of key shares

  // These should be defined in another module's package
  localparam int HealthStateWidth = 128;
  localparam int DevIdWidth = 256;

  // These should eventually be migrated to top level ports to ease integration changes
  // However there needs to be a strategy for top level to specific module connections,
  // instead of just intermodule.
  localparam logic[KeyWidth-1:0] RevisionSecret      = 256'hAAAA5555;
  localparam logic[KeyWidth-1:0] CreatorIdentityKey  = 256'hDEADBEEF;
  localparam logic[KeyWidth-1:0] OwnerIntIdentityKey = 256'hDEADBEEF;
  localparam logic[KeyWidth-1:0] OwnerIdentityKey    = 256'hDEADBEEF;
  localparam logic[KeyWidth-1:0] SoftOutputKey       = 256'hDEADBEEF;
  localparam logic[KeyWidth-1:0] HardOutputKey       = 256'hDEADBEEE;

  // Width calculations
  // These are the largest calculations in use across all stages
  localparam int AdvDataWidth = RomExtDescWidth + 2*KeyWidth + DevIdWidth + HealthStateWidth;
  localparam int IdDataWidth = KeyWidth;
  // key version + salt + key ID + constant
  localparam int GenDataWidth = 32 + 128 + 128 + KeyWidth;
  localparam int StageWidth = $clog2(KeyMgrStages);

  // Max Payload Width to derivation function
  // This should be decomposed to 1600 - security_strength*2
  // see security strength description https://keccak.team/keccak.html
  localparam int KDFMaxWidth = 1088;

  // Enumeration for operations
  typedef enum logic [2:0] {
    Creator   = 0,
    OwnerInt  = 1,
    Owner     = 2,
    Disable   = 3
  } keymgr_stage_e;

  // Enumeration for sideload sel
  typedef enum logic [1:0] {
    None   = 0,
    Aes    = 1,
    Hmac   = 2,
    Kmac   = 3
  } keymgr_key_dest_e;

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

  // Enumeration for working state
  typedef enum logic [2:0] {
    StReset = 0,
    StWipe = 1,
    StInit = 2,
    StCreatorRootKey = 3,
    StOwnerIntKey = 4,
    StOwnerKey = 5,
    StDisabled = 6,
    StWait = 7
  } keymgr_working_state_e;

  // Enumeration for operation status
  typedef enum logic [1:0] {
    OpIdle = 0,
    OpWip = 1,
    OpDoneSuccess = 2,
    OpDoneFail = 3
  } keymgr_op_status_e;

  // Enumeration for operation error
  // Errors are encoded as 1 type of error per bit
  typedef enum logic [3:0] {
    ErrInvalidOp = 0,
    ErrInvalidIn = 1,
    ErrInvalidOut = 2
  } keymgr_err_code_e;

  localparam int ErrWidth = $bits(keymgr_err_code_e);

  // Key connection to various modules
  typedef struct packed {
    logic valid;
    logic [KeyWidth-1:0] key_share0;
    logic [KeyWidth-1:0] key_share1;
  } hw_key_req_t;

  typedef struct packed {
    logic valid;
    logic [KmacDataIfWidth-1:0] data;
    logic [KmacDataIfWidth/8-1:0] strb;
  } kmac_data_req_t;

  typedef struct packed {
    logic ready;
    logic done;
    logic [KeyWidth-1:0] digest_share0;
    logic [KeyWidth-1:0] digest_share1;
  } kmac_data_rsp_t;

  parameter kmac_data_rsp_t KMAC_DATA_RSP_DEFAULT = ' {
    ready: 1'b1,
    done:  1'b1,
    digest_share0: '0,
    digest_share1: '0
  };

  // The following structs should be sourced from other modules
  // defined here temporarily
  typedef struct packed {
    logic [HealthStateWidth-1:0] health_state;
    logic keymgr_en;
  } lc_data_t;

  parameter lc_data_t LC_DATA_DEFAULT = ' {
    health_state: '0,
    keymgr_en:    1'b1
  };

  typedef struct packed {
    logic [DevIdWidth-1:0] devid;
    logic [KeyWidth-1:0] root_key;
  } otp_data_t;

  parameter otp_data_t OTP_DATA_DEFAULT = ' {
    devid:    '0,
    root_key: '0
  };

  typedef struct packed {
    logic div_key;
    logic [KeyWidth-1:0] owner_secret;
  } flash_key_t;

  parameter flash_key_t FLASH_KEY_DEFAULT = ' {
    div_key:      '0,
    owner_secret: '0
  };
endpackage : keymgr_pkg
