// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// key manager package
//

package keymgr_pkg;

  parameter int KeyWidth = 256;
  parameter int DigestWidth = 128;     // uses truncated hash
  parameter int KmacDataIfWidth = 64;  // KMAC interface data width
  parameter int KeyMgrStages = 3;      // Number of key manager stages (creator, ownerInt, owner)
  parameter int SwBindingWidth = 128; // Size of rom_ext hash, truncated
  parameter int Shares = 2; // number of key shares
  parameter int EdnWidth = edn_pkg::ENDPOINT_BUS_WIDTH;

  // These should be defined in another module's package
  parameter int HealthStateWidth = 128;
  parameter int DevIdWidth = 256;
  parameter int MaxWidth = 256;

  // Default seeds
  // These are generated using random.org byte dumper
  typedef logic [KeyWidth-1:0] seed_t;
  parameter seed_t RndCnstRevisionSeedDefault =
    256'h3a0a6d73cd50897de4d744bd65ebdb3837ea77087d878651c517c18a5742b2f9;
  parameter seed_t RndCnstCreatorIdentitySeedDefault =
    256'h6d234651d535ebb0dce4d82f503096614355fc7b84595e4f67a866177d421df6;
  parameter seed_t RndCnstOwnerIntIdentitySeedDefault =
    256'hdba98db4fb1413b32fd5a4deac3ce546966a4bc2761235643358c8e76083d382;
  parameter seed_t RndCnstOwnerIdentitySeedDefault =
    256'h8c0a27ef53e0e0bf5f5f5e26a30a0d0db10761ed802c6d2fd22873209976021e;
  parameter seed_t RndCnstSoftOutputSeedDefault =
    256'h99cadb2c2d9b438591d943a89bc64dbb3bc2abc842eeea5faf74d27f7a7c99b6;
  parameter seed_t RndCnstHardOutputSeedDefault =
    256'hd551b351decbb6f687c7f5c845363f12d6411fae812e16b23bc8ae59885a56b1;

  // Target based deriviation seeds
  // These are used during the generation stages for sideload
  parameter seed_t RndCnstNoneSeedDefault =
    256'h6EECBF9FC3C64230421DA1EAEC48F871070A3582E71AD4059D5D550784E9B9DE;
  parameter seed_t RndCnstAesSeedDefault =
    256'hC1104CD94EBA084FA6438188038006489F3DF38771214AE0BBA65CEB9BC2366F;
  parameter seed_t RndCnstHmacSeedDefault =
    256'h075CF7939313EEC797019BD0036D9500374A8FD9121CC8E78E1E3359D5F77C4E;
  parameter seed_t RndCnstKmacSeedDefault =
    256'h0A5CCCD9627BF6169B3A765D3D6D0CD89DBDCB7B6DF8D3C03746D60A0145D3ED;

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
  parameter int GenDataWidth = 32 + 128 + KeyWidth*2;
  parameter int StageWidth = $clog2(KeyMgrStages);

  // Max Payload Width to derivation function
  // This should be decomposed to 1600 - security_strength*2
  // see security strength description https://keccak.team/keccak.html
  parameter int KDFMaxWidth = 1088;

  // Enumeration for operations
  typedef enum logic [2:0] {
    Creator   = 0,
    OwnerInt  = 1,
    Owner     = 2,
    Disable   = 3
  } keymgr_stage_e;

  // Enumeration for sideload sel
  typedef enum logic [2:0] {
    None,
    Aes,
    Hmac,
    Kmac
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

  // Bit position of error code
  // Error is encoded as 1 error per bit
  typedef enum logic [2:0] {
    ErrInvalidOp,
    ErrInvalidCmd,
    ErrInvalidIn,
    ErrInvalidOut,
    ErrLastPos
  } keymgr_err_pos_e;

  typedef enum logic [2:0] {
    KeyUpdateIdle,
    KeyUpdateRandom,
    KeyUpdateRoot,
    KeyUpdateKmac,
    KeyUpdateInvalid,
    KeyUpdateWipe
  } keymgr_key_update_e;

  // Key connection to various modules
  typedef struct packed {
    logic valid;
    logic [KeyWidth-1:0] key_share0;
    logic [KeyWidth-1:0] key_share1;
  } hw_key_req_t;

  parameter hw_key_req_t HW_KEY_REQ_DEFAULT = '{
    valid: 1'b0,
    key_share0: KeyWidth'(32'hDEADBEEF),
    key_share1: KeyWidth'(32'hFACEBEEF)
  };

  typedef struct packed {
    logic valid;
    logic [KmacDataIfWidth-1:0] data;
    logic [KmacDataIfWidth/8-1:0] strb;
    // last indicates the last beat of the data. strb can be partial only with
    // last.
    logic last;
  } kmac_data_req_t;

  typedef struct packed {
    logic ready;
    logic done;
    logic [KeyWidth-1:0] digest_share0;
    logic [KeyWidth-1:0] digest_share1;
    // Error is valid when done is high. If any error occurs during KDF, KMAC
    // returns the garbage digest data with error. The KeyMgr discards the
    // digest and may re-initiate the process.
    logic error;
  } kmac_data_rsp_t;

  parameter kmac_data_req_t KMAC_DATA_REQ_DEFAULT = '{
    valid: 1'b 0,
    data: '0,
    strb: '0,
    last: 1'b 0
  };
  parameter kmac_data_rsp_t KMAC_DATA_RSP_DEFAULT = '{
    ready: 1'b1,
    done:  1'b1,
    digest_share0: KeyWidth'(32'hDEADBEEF),
    digest_share1: KeyWidth'(32'hFACEBEEF),
    error: 1'b1
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

  // TODO: this will be removed later once the device ID information
  // is broadcasted
  typedef struct packed {
    logic [DevIdWidth-1:0] devid;
  } otp_data_t;

  parameter otp_data_t OTP_DATA_DEFAULT = '{
    devid:    '0
  };


  // perm_data
  function automatic logic[RandWidth-1:0] perm_data (logic [RandWidth-1:0] data,
    rand_perm_t perm_sel);

    for (int k = 0; k < 32; k++) begin : gen_data_loop
      perm_data[k] = data[perm_sel[k]];
    end

  endfunction

endpackage : keymgr_pkg
