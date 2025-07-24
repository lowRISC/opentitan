// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Package partition metadata.
//
package otp_ctrl_part_pkg;

  import prim_util_pkg::vbits;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_pkg::*;
  import otp_ctrl_top_specific_pkg::*;

  ////////////////////////////////////
  // Scrambling Constants and Types //
  ////////////////////////////////////

  parameter int NumScrmblKeys = 4;
  parameter int NumDigestSets = 2;

  parameter int ScrmblKeySelWidth = vbits(NumScrmblKeys);
  parameter int DigestSetSelWidth = vbits(NumDigestSets);
  parameter int ConstSelWidth = (ScrmblKeySelWidth > DigestSetSelWidth) ?
                                ScrmblKeySelWidth :
                                DigestSetSelWidth;

  typedef enum logic [ConstSelWidth-1:0] {
    StandardMode,
    ChainedMode
  } digest_mode_e;

  typedef logic [NumScrmblKeys-1:0][ScrmblKeyWidth-1:0] key_array_t;
  typedef logic [NumDigestSets-1:0][ScrmblKeyWidth-1:0] digest_const_array_t;
  typedef logic [NumDigestSets-1:0][ScrmblBlockWidth-1:0] digest_iv_array_t;

  typedef enum logic [ConstSelWidth-1:0] {
    Secret0Key,
    Secret1Key,
    Secret2Key,
    Secret3Key
  } key_sel_e;

  typedef enum logic [ConstSelWidth-1:0] {
    CnstyDigest,
    SramDataKey
  } digest_sel_e;

  // SEC_CM: SECRET.MEM.SCRAMBLE
  parameter key_array_t RndCnstKey = {
    128'hBEAD91D5FA4E09150E95F517CB98955B,
    128'h85A9E830BC059BA9286D6E2856A05CC3,
    128'hEFFA6D736C5EFF49AE7B70F9C46E5A62,
    128'h3BA121C5E097DDEB7768B4C666E9C3DA
  };

  // SEC_CM: PART.MEM.DIGEST
  // Note: digest set 0 is used for computing the partition digests. Constants at
  // higher indices are used to compute the scrambling keys.
  parameter digest_const_array_t RndCnstDigestConst = {
    128'hB7474D640F8A7F5D60822E1FAEC5C72,
    128'hE048B657396B4B83277195FC471E4B26
  };

  parameter digest_iv_array_t RndCnstDigestIV = {
    64'hB6641214B61D1B43,
    64'h4D5A89AA9109294A
  };


  /////////////////////////////////////
  // Typedefs for Partition Metadata //
  /////////////////////////////////////

  typedef enum logic [1:0] {
    Unbuffered,
    Buffered,
    LifeCycle
  } part_variant_e;

  typedef struct packed {
    part_variant_e variant;
    // Offset and size within the OTP array, in Bytes.
    logic [OtpByteAddrWidth-1:0] offset;
    logic [OtpByteAddrWidth-1:0] size;
    // Key index to use for scrambling.
    key_sel_e key_sel;
    // Attributes
    logic secret;           // Whether the partition is secret (and hence scrambled)
    logic sw_digest;        // Whether the partition has a software digest
    logic hw_digest;        // Whether the partition has a hardware digest
    logic write_lock;       // Whether the partition is write lockable (via digest)
    logic read_lock;        // Whether the partition is read lockable (via digest)
    logic integrity;        // Whether the partition is integrity protected
    logic iskeymgr_creator; // Whether the partition has any creator key material
    logic iskeymgr_owner;   // Whether the partition has any owner key material
    logic zeroizable;       // Whether the partition can be zeroized
  } part_info_t;

  parameter part_info_t PartInfoDefault = '{
      variant:          Unbuffered,
      offset:           '0,
      size:             OtpByteAddrWidth'('hFF),
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b0,
      hw_digest:        1'b0,
      write_lock:       1'b0,
      read_lock:        1'b0,
      integrity:        1'b0,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b0
  };

  ////////////////////////
  // Partition Metadata //
  ////////////////////////

  localparam part_info_t PartInfo [NumPart] = '{
    // VENDOR_TEST
    '{
      variant:          Unbuffered,
      offset:           14'd0,
      size:             72,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b0,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // CREATOR_SW_CFG
    '{
      variant:          Unbuffered,
      offset:           14'd72,
      size:             312,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // OWNER_SW_CFG
    '{
      variant:          Unbuffered,
      offset:           14'd384,
      size:             624,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // OWNERSHIP_SLOT_STATE
    '{
      variant:          Unbuffered,
      offset:           14'd1008,
      size:             56,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b0,
      hw_digest:        1'b0,
      write_lock:       1'b0,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // ROT_CREATOR_AUTH
    '{
      variant:          Unbuffered,
      offset:           14'd1064,
      size:             1432,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // ROT_OWNER_AUTH_SLOT0
    '{
      variant:          Unbuffered,
      offset:           14'd2496,
      size:             336,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // ROT_OWNER_AUTH_SLOT1
    '{
      variant:          Unbuffered,
      offset:           14'd2832,
      size:             336,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // PLAT_INTEG_AUTH_SLOT0
    '{
      variant:          Unbuffered,
      offset:           14'd3168,
      size:             336,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // PLAT_INTEG_AUTH_SLOT1
    '{
      variant:          Unbuffered,
      offset:           14'd3504,
      size:             336,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // PLAT_OWNER_AUTH_SLOT0
    '{
      variant:          Unbuffered,
      offset:           14'd3840,
      size:             336,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // PLAT_OWNER_AUTH_SLOT1
    '{
      variant:          Unbuffered,
      offset:           14'd4176,
      size:             336,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // PLAT_OWNER_AUTH_SLOT2
    '{
      variant:          Unbuffered,
      offset:           14'd4512,
      size:             336,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // PLAT_OWNER_AUTH_SLOT3
    '{
      variant:          Unbuffered,
      offset:           14'd4848,
      size:             336,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // EXT_NVM
    '{
      variant:          Unbuffered,
      offset:           14'd5184,
      size:             1032,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b0,
      hw_digest:        1'b0,
      write_lock:       1'b0,
      read_lock:        1'b0,
      integrity:        1'b0,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // ROM_PATCH
    '{
      variant:          Unbuffered,
      offset:           14'd6216,
      size:             9720,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // HW_CFG0
    '{
      variant:          Buffered,
      offset:           14'd15936,
      size:             80,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b0,
      hw_digest:        1'b1,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // HW_CFG1
    '{
      variant:          Buffered,
      offset:           14'd16016,
      size:             24,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b0,
      hw_digest:        1'b1,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // SECRET0
    '{
      variant:          Buffered,
      offset:           14'd16040,
      size:             48,
      key_sel:          Secret0Key,
      secret:           1'b1,
      sw_digest:        1'b0,
      hw_digest:        1'b1,
      write_lock:       1'b1,
      read_lock:        1'b1,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // SECRET1
    '{
      variant:          Buffered,
      offset:           14'd16088,
      size:             32,
      key_sel:          Secret1Key,
      secret:           1'b1,
      sw_digest:        1'b0,
      hw_digest:        1'b1,
      write_lock:       1'b1,
      read_lock:        1'b1,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // SECRET2
    '{
      variant:          Buffered,
      offset:           14'd16120,
      size:             128,
      key_sel:          Secret2Key,
      secret:           1'b1,
      sw_digest:        1'b0,
      hw_digest:        1'b1,
      write_lock:       1'b1,
      read_lock:        1'b1,
      integrity:        1'b1,
      iskeymgr_creator: 1'b1,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b1
    },
    // SECRET3
    '{
      variant:          Buffered,
      offset:           14'd16248,
      size:             48,
      key_sel:          Secret3Key,
      secret:           1'b1,
      sw_digest:        1'b0,
      hw_digest:        1'b1,
      write_lock:       1'b1,
      read_lock:        1'b1,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b1,
      zeroizable:       1'b1
    },
    // LIFE_CYCLE
    '{
      variant:          LifeCycle,
      offset:           14'd16296,
      size:             88,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b0,
      hw_digest:        1'b0,
      write_lock:       1'b0,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b0
    }
  };

  typedef enum {
    VendorTestIdx,
    CreatorSwCfgIdx,
    OwnerSwCfgIdx,
    OwnershipSlotStateIdx,
    RotCreatorAuthIdx,
    RotOwnerAuthSlot0Idx,
    RotOwnerAuthSlot1Idx,
    PlatIntegAuthSlot0Idx,
    PlatIntegAuthSlot1Idx,
    PlatOwnerAuthSlot0Idx,
    PlatOwnerAuthSlot1Idx,
    PlatOwnerAuthSlot2Idx,
    PlatOwnerAuthSlot3Idx,
    ExtNvmIdx,
    RomPatchIdx,
    HwCfg0Idx,
    HwCfg1Idx,
    Secret0Idx,
    Secret1Idx,
    Secret2Idx,
    Secret3Idx,
    LifeCycleIdx,
    // These are not "real partitions", but in terms of implementation it is convenient to
    // add these at the end of certain arrays.
    DaiIdx,
    LciIdx,
    KdiIdx,
    // Number of agents is the last idx+1.
    NumAgentsIdx
  } part_idx_e;

  parameter int NumAgents = int'(NumAgentsIdx);

  // Breakout types for easier access of individual items.
  typedef struct packed {
    logic [255:0] manuf_state;
    logic [255:0] device_id;
  } otp_hw_cfg0_data_t;

  // default value used for intermodule
  parameter otp_hw_cfg0_data_t OTP_HW_CFG0_DATA_DEFAULT = '{
    manuf_state: 256'h63B9485A3856C417CF7A50A9A91EF7F7B3A5B4421F462370FFF698183664DC7E,
    device_id: 256'h90C7F21F6224F027F98C48B1F93772844A22D4B78FE0266FBEE3958332F2939B
  };
  typedef struct packed {
    logic [15:0] unallocated;
    prim_mubi_pkg::mubi8_t en_sram_ifetch;
    prim_mubi_pkg::mubi8_t en_csrng_sw_app_read;
    logic [31:0] soc_dbg_state;
  } otp_hw_cfg1_data_t;

  // default value used for intermodule
  parameter otp_hw_cfg1_data_t OTP_HW_CFG1_DATA_DEFAULT = '{
    unallocated: 16'h0,
    en_sram_ifetch: prim_mubi_pkg::mubi8_t'(8'h69),
    en_csrng_sw_app_read: prim_mubi_pkg::mubi8_t'(8'h69),
    soc_dbg_state: 32'h0
  };
  typedef struct packed {
    // This reuses the same encoding as the life cycle signals for indicating valid status.
    lc_ctrl_pkg::lc_tx_t valid;
    otp_hw_cfg1_data_t hw_cfg1_data;
    otp_hw_cfg0_data_t hw_cfg0_data;
  } otp_broadcast_t;

  // default value for intermodule
  parameter otp_broadcast_t OTP_BROADCAST_DEFAULT = '{
    valid: lc_ctrl_pkg::Off,
    hw_cfg1_data: OTP_HW_CFG1_DATA_DEFAULT,
    hw_cfg0_data: OTP_HW_CFG0_DATA_DEFAULT
  };


  // OTP invalid partition default for all partitions.
  parameter logic [131071:0] PartInvDefault = 131072'({
    // LIFE_CYCLE default
    704'({
      // LC_STATE
      320'h1136C663A36C3E3E817E760B27AE937BFCDF15A3429452A851B80674A2B6FBE93B61DE417B9FB33,
      // LC_TRANSITION_CNT
      384'hD68C96F0B3D1FEED688098A43C33459F0279FC51CC7C626E315FD2B871D88819A0D1E90E8C9FDDFA01E46311FD36D954
    }),
    // SECRET3 default
    384'({
      // SECRET3_ZER
      64'h0,
      // SECRET3_DIGEST
      64'h3BF7D79A9FF747F6,
      // OWNER_SEED
      256'hD0BAC511D08ECE0E2C0DBDDEDF7A854D5E58D0AA97A0F8F6D3D58610F4851667
    }),
    // SECRET2 default
    1024'({
      // SECRET2_ZER
      64'h0,
      // SECRET2_DIGEST
      64'h41837480464544A1,
      // CREATOR_SEED
      256'hE00E9680BD9B70291C752824C7DDC89694CD3DED94B578192A4D8B51F5D41C8A,
      // CREATOR_ROOT_KEY_SHARE1
      256'h105733EAA3880C5A234729143F97B62A55D0320379A0D260426D99D374E699CA,
      // CREATOR_ROOT_KEY_SHARE0
      256'hDBC827839FE2DCC27E17D06B5D4E0DDDDBB9844327F20FB5D396D1CE085BDC31,
      // RMA_TOKEN
      128'h711D135F59A50322B6711DB6F5D40A37
    }),
    // SECRET1 default
    256'({
      // SECRET1_ZER
      64'h0,
      // SECRET1_DIGEST
      64'h6FDFE93D3146B0F,
      // SRAM_DATA_KEY_SEED
      128'hB5AC1F53D00A08C3B28B5C0FEE5F4C02
    }),
    // SECRET0 default
    384'({
      // SECRET0_ZER
      64'h0,
      // SECRET0_DIGEST
      64'h67BBE3B4555DF35C,
      // TEST_EXIT_TOKEN
      128'h40119A3C6E63CDF358840E458E4029A6,
      // TEST_UNLOCK_TOKEN
      128'hDF3888886BD10DC67ABB319BDA0529AE
    }),
    // HW_CFG1 default
    192'({
      // HW_CFG1_ZER
      64'h0,
      // HW_CFG1_DIGEST
      64'hAA3F4C71234F097C,
      // EN_SRAM_IFETCH
      16'h0, // unallocated 2 bytes
      8'h69,
      // EN_CSRNG_SW_APP_READ
      8'h69,
      // SOC_DBG_STATE
      32'h0
    }),
    // HW_CFG0 default
    640'({
      // HW_CFG0_ZER
      64'h0,
      // HW_CFG0_DIGEST
      64'h8CBBAD02BB4CA928,
      // MANUF_STATE
      256'h63B9485A3856C417CF7A50A9A91EF7F7B3A5B4421F462370FFF698183664DC7E,
      // DEVICE_ID
      256'h90C7F21F6224F027F98C48B1F93772844A22D4B78FE0266FBEE3958332F2939B
    }),
    // ROM_PATCH default
    77760'({
      // ROM_PATCH_ZER
      64'h0,
      // ROM_PATCH_DIGEST
      64'hC469C593E5DC0DA8,
      // ROM_PATCH_DATA
      4096'h0, // unallocated 512 bytes
      73536'h0
    }),
    // EXT_NVM default
    8256'({
      // EXT_NVM_ZER
      64'h0,
      // EXT_NVM_ANTIREPLAY_FRESHNESS_CNT
      8192'h0
    }),
    // PLAT_OWNER_AUTH_SLOT3 default
    2688'({
      // PLAT_OWNER_AUTH_SLOT3_ZER
      64'h0,
      // PLAT_OWNER_AUTH_SLOT3_DIGEST
      64'hBE193854E9CA60A0,
      // PLAT_OWNER_AUTH_SLOT3_UNLOCK4XFER_KEY
      1280'h0,
      // PLAT_OWNER_AUTH_SLOT3_KEYMANIFEST_KEY
      1280'h0
    }),
    // PLAT_OWNER_AUTH_SLOT2 default
    2688'({
      // PLAT_OWNER_AUTH_SLOT2_ZER
      64'h0,
      // PLAT_OWNER_AUTH_SLOT2_DIGEST
      64'hBBF4A76885E754F2,
      // PLAT_OWNER_AUTH_SLOT2_UNLOCK4XFER_KEY
      1280'h0,
      // PLAT_OWNER_AUTH_SLOT2_KEYMANIFEST_KEY
      1280'h0
    }),
    // PLAT_OWNER_AUTH_SLOT1 default
    2688'({
      // PLAT_OWNER_AUTH_SLOT1_ZER
      64'h0,
      // PLAT_OWNER_AUTH_SLOT1_DIGEST
      64'hF87BED95CFBA3727,
      // PLAT_OWNER_AUTH_SLOT1_UNLOCK4XFER_KEY
      1280'h0,
      // PLAT_OWNER_AUTH_SLOT1_KEYMANIFEST_KEY
      1280'h0
    }),
    // PLAT_OWNER_AUTH_SLOT0 default
    2688'({
      // PLAT_OWNER_AUTH_SLOT0_ZER
      64'h0,
      // PLAT_OWNER_AUTH_SLOT0_DIGEST
      64'h20440F25BB053FB5,
      // PLAT_OWNER_AUTH_SLOT0_UNLOCK4XFER_KEY
      1280'h0,
      // PLAT_OWNER_AUTH_SLOT0_KEYMANIFEST_KEY
      1280'h0
    }),
    // PLAT_INTEG_AUTH_SLOT1 default
    2688'({
      // PLAT_INTEG_AUTH_SLOT1_ZER
      64'h0,
      // PLAT_INTEG_AUTH_SLOT1_DIGEST
      64'h15F164D7930C9D19,
      // PLAT_INTEG_AUTH_SLOT1_UNLOCK4XFER_KEY
      1280'h0,
      // PLAT_INTEG_AUTH_SLOT1_KEYMANIFEST_KEY
      1280'h0
    }),
    // PLAT_INTEG_AUTH_SLOT0 default
    2688'({
      // PLAT_INTEG_AUTH_SLOT0_ZER
      64'h0,
      // PLAT_INTEG_AUTH_SLOT0_DIGEST
      64'hE29749216775E8A5,
      // PLAT_INTEG_AUTH_SLOT0_UNLOCK4XFER_KEY
      1280'h0,
      // PLAT_INTEG_AUTH_SLOT0_KEYMANIFEST_KEY
      1280'h0
    }),
    // ROT_OWNER_AUTH_SLOT1 default
    2688'({
      // ROT_OWNER_AUTH_SLOT1_ZER
      64'h0,
      // ROT_OWNER_AUTH_SLOT1_DIGEST
      64'h340A5B93BB19342,
      // ROT_OWNER_AUTH_SLOT1_UNLOCK4XFER_KEY
      1280'h0,
      // ROT_OWNER_AUTH_SLOT1_KEYMANIFEST_KEY
      1280'h0
    }),
    // ROT_OWNER_AUTH_SLOT0 default
    2688'({
      // ROT_OWNER_AUTH_SLOT0_ZER
      64'h0,
      // ROT_OWNER_AUTH_SLOT0_DIGEST
      64'h4947DD361344767A,
      // ROT_OWNER_AUTH_SLOT0_UNLOCK4XFER_KEY
      1280'h0,
      // ROT_OWNER_AUTH_SLOT0_KEYMANIFEST_KEY
      1280'h0
    }),
    // ROT_CREATOR_AUTH default
    11456'({
      // ROT_CREATOR_AUTH_ZER
      64'h0,
      // ROT_CREATOR_AUTH_DIGEST
      64'hA445C3C29F71A256,
      // ROT_CREATOR_AUTH_IDENTITY_CERT
      32'h0, // unallocated 4 bytes
      6144'h0,
      // ROT_CREATOR_AUTH_UNLOCK4XFER_KEY
      1280'h0,
      // ROT_CREATOR_AUTH_KEYMANIFEST_KEY
      1280'h0,
      // ROT_CREATOR_AUTH_ROM2_PATCH_SIGVERIFY_KEY
      1280'h0,
      // ROT_CREATOR_AUTH_OWNERSHIP_STATE
      32'h0,
      // ROT_CREATOR_AUTH_NON_RAW_MFW_CODESIGN_KEY
      1280'h0
    }),
    // OWNERSHIP_SLOT_STATE default
    448'({
      // OWNERSHIP_SLOT_STATE_ZER
      64'h0,
      // OWNERSHIP_SLOT_STATE_PLAT_OWNER_AUTH
      128'h0,
      // OWNERSHIP_SLOT_STATE_PLAT_INTEG_AUTH
      128'h0,
      // OWNERSHIP_SLOT_STATE_ROT_OWNER_AUTH
      128'h0
    }),
    // OWNER_SW_CFG default
    4992'({
      // OWNER_SW_CFG_ZER
      64'h0,
      // OWNER_SW_CFG_DIGEST
      64'h3E725E464F593C87,
      // OWNER_SW_CFG_ROM_RSTMGR_INFO_EN
      32'h0,
      // OWNER_SW_CFG_MANUF_STATE
      32'h0,
      // OWNER_SW_CFG_ROM_KEYMGR_ROM_EXT_MEAS_EN
      32'h0,
      // OWNER_SW_CFG_ROM_WATCHDOG_BITE_THRESHOLD_CYCLES
      32'h0,
      // OWNER_SW_CFG_ROM_ALERT_DIGEST_RMA
      32'h0,
      // OWNER_SW_CFG_ROM_ALERT_DIGEST_DEV
      32'h0,
      // OWNER_SW_CFG_ROM_ALERT_DIGEST_PROD_END
      32'h0,
      // OWNER_SW_CFG_ROM_ALERT_DIGEST_PROD
      32'h0,
      // OWNER_SW_CFG_ROM_ALERT_PHASE_CYCLES
      512'h0,
      // OWNER_SW_CFG_ROM_ALERT_TIMEOUT_CYCLES
      128'h0,
      // OWNER_SW_CFG_ROM_ALERT_ACCUM_THRESH
      128'h0,
      // OWNER_SW_CFG_ROM_LOCAL_ALERT_CLASSIFICATION
      512'h0,
      // OWNER_SW_CFG_ROM_ALERT_CLASSIFICATION
      3200'h0,
      // OWNER_SW_CFG_ROM_ALERT_ESCALATION
      32'h0,
      // OWNER_SW_CFG_ROM_ALERT_CLASS_EN
      32'h0,
      // OWNER_SW_CFG_ROM_BOOTSTRAP_DIS
      32'h0,
      // OWNER_SW_CFG_ROM_ERROR_REPORTING
      32'h0
    }),
    // CREATOR_SW_CFG default
    2496'({
      // CREATOR_SW_CFG_ZER
      64'h0,
      // CREATOR_SW_CFG_DIGEST
      64'hCC6596C7174EBA64,
      // CREATOR_SW_CFG_SRAM_KEY_RENEW_EN
      32'h0, // unallocated 4 bytes
      32'h0,
      // CREATOR_SW_CFG_RNG_HEALTH_CONFIG_DIGEST
      32'h0,
      // CREATOR_SW_CFG_RNG_ALERT_THRESHOLD
      32'h0,
      // CREATOR_SW_CFG_RNG_EXTHT_LO_THRESHOLDS
      32'h0,
      // CREATOR_SW_CFG_RNG_EXTHT_HI_THRESHOLDS
      32'h0,
      // CREATOR_SW_CFG_RNG_MARKOV_LO_THRESHOLDS
      32'h0,
      // CREATOR_SW_CFG_RNG_MARKOV_HI_THRESHOLDS
      32'h0,
      // CREATOR_SW_CFG_RNG_BUCKET_THRESHOLDS
      32'h0,
      // CREATOR_SW_CFG_RNG_ADAPTP_LO_THRESHOLDS
      32'h0,
      // CREATOR_SW_CFG_RNG_ADAPTP_HI_THRESHOLDS
      32'h0,
      // CREATOR_SW_CFG_RNG_REPCNTS_THRESHOLDS
      32'h0,
      // CREATOR_SW_CFG_RNG_REPCNT_THRESHOLDS
      32'h0,
      // CREATOR_SW_CFG_RMA_SPIN_CYCLES
      32'h0,
      // CREATOR_SW_CFG_RMA_SPIN_EN
      32'h0,
      // CREATOR_SW_CFG_DEFAULT_BOOT_DATA_IN_PROD_EN
      32'h0,
      // CREATOR_SW_CFG_MIN_SEC_VER_BL0
      32'h0,
      // CREATOR_SW_CFG_MIN_SEC_VER_ROM_EXT
      32'h0,
      // CREATOR_SW_CFG_CPUCTRL
      32'h0,
      // CREATOR_SW_CFG_ROM_EXEC_EN
      32'h0,
      // CREATOR_SW_CFG_MANUF_STATE
      32'h0,
      // CREATOR_SW_CFG_RET_RAM_RESET_MASK
      32'h0,
      // CREATOR_SW_CFG_JITTER_EN
      32'h0,
      // CREATOR_SW_CFG_RNG_EN
      32'h0,
      // CREATOR_SW_CFG_FLASH_HW_INFO_CFG_OVERRIDE
      32'h0,
      // CREATOR_SW_CFG_FLASH_INFO_BOOT_DATA_CFG
      32'h0,
      // CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG
      32'h0,
      // CREATOR_SW_CFG_SIGVERIFY_SPX_KEY_EN
      64'h0,
      // CREATOR_SW_CFG_SIGVERIFY_SPX_EN
      32'h0,
      // CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN
      64'h0,
      // CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN
      32'h0,
      // CREATOR_SW_CFG_ROM_EXT_SKU
      32'h0,
      // CREATOR_SW_CFG_OVERRIDES
      256'h0,
      // CREATOR_SW_CFG_AST_INIT_EN
      32'h0,
      // CREATOR_SW_CFG_AST_CFG
      992'h0
    }),
    // VENDOR_TEST default
    576'({
      // VENDOR_TEST_ZER
      64'h0,
      // VENDOR_TEST_DIGEST
      64'h9605F051E74379CB,
      // SCRATCH
      448'h0
    })});

  ///////////////////////////////////////////////
  // Parameterized Assignment Helper Functions //
  ///////////////////////////////////////////////

  function automatic otp_ctrl_core_hw2reg_t named_reg_assign(
      logic [NumPart-1:0][ScrmblBlockWidth-1:0] part_digest);
    otp_ctrl_core_hw2reg_t hw2reg;
    logic unused_sigs;
    unused_sigs = ^part_digest;
    hw2reg = '0;
    hw2reg.vendor_test_digest = part_digest[VendorTestIdx];
    hw2reg.creator_sw_cfg_digest = part_digest[CreatorSwCfgIdx];
    hw2reg.owner_sw_cfg_digest = part_digest[OwnerSwCfgIdx];
    hw2reg.rot_creator_auth_digest = part_digest[RotCreatorAuthIdx];
    hw2reg.rot_owner_auth_slot0_digest = part_digest[RotOwnerAuthSlot0Idx];
    hw2reg.rot_owner_auth_slot1_digest = part_digest[RotOwnerAuthSlot1Idx];
    hw2reg.plat_integ_auth_slot0_digest = part_digest[PlatIntegAuthSlot0Idx];
    hw2reg.plat_integ_auth_slot1_digest = part_digest[PlatIntegAuthSlot1Idx];
    hw2reg.plat_owner_auth_slot0_digest = part_digest[PlatOwnerAuthSlot0Idx];
    hw2reg.plat_owner_auth_slot1_digest = part_digest[PlatOwnerAuthSlot1Idx];
    hw2reg.plat_owner_auth_slot2_digest = part_digest[PlatOwnerAuthSlot2Idx];
    hw2reg.plat_owner_auth_slot3_digest = part_digest[PlatOwnerAuthSlot3Idx];
    hw2reg.rom_patch_digest = part_digest[RomPatchIdx];
    hw2reg.hw_cfg0_digest = part_digest[HwCfg0Idx];
    hw2reg.hw_cfg1_digest = part_digest[HwCfg1Idx];
    hw2reg.secret0_digest = part_digest[Secret0Idx];
    hw2reg.secret1_digest = part_digest[Secret1Idx];
    hw2reg.secret2_digest = part_digest[Secret2Idx];
    hw2reg.secret3_digest = part_digest[Secret3Idx];
    return hw2reg;
  endfunction : named_reg_assign

  function automatic part_access_t [NumPart-1:0] named_part_access_pre(
      otp_ctrl_core_reg2hw_t reg2hw);
    part_access_t [NumPart-1:0] part_access_pre;
    logic unused_sigs;
    unused_sigs = ^reg2hw;
    // Default (this will be overridden by partition-internal settings).
    part_access_pre = {{32'(2*NumPart)}{prim_mubi_pkg::MuBi8False}};
    // Note: these could be made a MuBi CSRs in the future.
    // The main thing that is missing right now is proper support for W0C.
    // VENDOR_TEST
    if (!reg2hw.vendor_test_read_lock) begin
      part_access_pre[VendorTestIdx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    // CREATOR_SW_CFG
    if (!reg2hw.creator_sw_cfg_read_lock) begin
      part_access_pre[CreatorSwCfgIdx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    // OWNER_SW_CFG
    if (!reg2hw.owner_sw_cfg_read_lock) begin
      part_access_pre[OwnerSwCfgIdx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    // OWNERSHIP_SLOT_STATE
    if (!reg2hw.ownership_slot_state_read_lock) begin
      part_access_pre[OwnershipSlotStateIdx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    // ROT_CREATOR_AUTH
    if (!reg2hw.rot_creator_auth_read_lock) begin
      part_access_pre[RotCreatorAuthIdx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    // ROT_OWNER_AUTH_SLOT0
    if (!reg2hw.rot_owner_auth_slot0_read_lock) begin
      part_access_pre[RotOwnerAuthSlot0Idx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    // ROT_OWNER_AUTH_SLOT1
    if (!reg2hw.rot_owner_auth_slot1_read_lock) begin
      part_access_pre[RotOwnerAuthSlot1Idx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    // PLAT_INTEG_AUTH_SLOT0
    if (!reg2hw.plat_integ_auth_slot0_read_lock) begin
      part_access_pre[PlatIntegAuthSlot0Idx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    // PLAT_INTEG_AUTH_SLOT1
    if (!reg2hw.plat_integ_auth_slot1_read_lock) begin
      part_access_pre[PlatIntegAuthSlot1Idx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    // PLAT_OWNER_AUTH_SLOT0
    if (!reg2hw.plat_owner_auth_slot0_read_lock) begin
      part_access_pre[PlatOwnerAuthSlot0Idx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    // PLAT_OWNER_AUTH_SLOT1
    if (!reg2hw.plat_owner_auth_slot1_read_lock) begin
      part_access_pre[PlatOwnerAuthSlot1Idx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    // PLAT_OWNER_AUTH_SLOT2
    if (!reg2hw.plat_owner_auth_slot2_read_lock) begin
      part_access_pre[PlatOwnerAuthSlot2Idx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    // PLAT_OWNER_AUTH_SLOT3
    if (!reg2hw.plat_owner_auth_slot3_read_lock) begin
      part_access_pre[PlatOwnerAuthSlot3Idx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    // EXT_NVM
    if (!reg2hw.ext_nvm_read_lock) begin
      part_access_pre[ExtNvmIdx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    // ROM_PATCH
    if (!reg2hw.rom_patch_read_lock) begin
      part_access_pre[RomPatchIdx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    return part_access_pre;
  endfunction : named_part_access_pre

  // Create the broadcast data from specific partitions excluding digests since they
  // are of no use for consumers of this data data.
  function automatic otp_broadcast_t named_broadcast_assign(
      logic [NumPart-1:0] part_init_done,
      logic [$bits(PartInvDefault)/8-1:0][7:0] part_buf_data);
    otp_broadcast_t otp_broadcast;
    logic valid, unused;
    unused = 1'b0;
    valid = 1'b1;
    // VENDOR_TEST
    unused ^= ^{part_init_done[VendorTestIdx],
                part_buf_data[VendorTestOffset +: VendorTestSize]};
    // CREATOR_SW_CFG
    unused ^= ^{part_init_done[CreatorSwCfgIdx],
                part_buf_data[CreatorSwCfgOffset +: CreatorSwCfgSize]};
    // OWNER_SW_CFG
    unused ^= ^{part_init_done[OwnerSwCfgIdx],
                part_buf_data[OwnerSwCfgOffset +: OwnerSwCfgSize]};
    // OWNERSHIP_SLOT_STATE
    unused ^= ^{part_init_done[OwnershipSlotStateIdx],
                part_buf_data[OwnershipSlotStateOffset +: OwnershipSlotStateSize]};
    // ROT_CREATOR_AUTH
    unused ^= ^{part_init_done[RotCreatorAuthIdx],
                part_buf_data[RotCreatorAuthOffset +: RotCreatorAuthSize]};
    // ROT_OWNER_AUTH_SLOT0
    unused ^= ^{part_init_done[RotOwnerAuthSlot0Idx],
                part_buf_data[RotOwnerAuthSlot0Offset +: RotOwnerAuthSlot0Size]};
    // ROT_OWNER_AUTH_SLOT1
    unused ^= ^{part_init_done[RotOwnerAuthSlot1Idx],
                part_buf_data[RotOwnerAuthSlot1Offset +: RotOwnerAuthSlot1Size]};
    // PLAT_INTEG_AUTH_SLOT0
    unused ^= ^{part_init_done[PlatIntegAuthSlot0Idx],
                part_buf_data[PlatIntegAuthSlot0Offset +: PlatIntegAuthSlot0Size]};
    // PLAT_INTEG_AUTH_SLOT1
    unused ^= ^{part_init_done[PlatIntegAuthSlot1Idx],
                part_buf_data[PlatIntegAuthSlot1Offset +: PlatIntegAuthSlot1Size]};
    // PLAT_OWNER_AUTH_SLOT0
    unused ^= ^{part_init_done[PlatOwnerAuthSlot0Idx],
                part_buf_data[PlatOwnerAuthSlot0Offset +: PlatOwnerAuthSlot0Size]};
    // PLAT_OWNER_AUTH_SLOT1
    unused ^= ^{part_init_done[PlatOwnerAuthSlot1Idx],
                part_buf_data[PlatOwnerAuthSlot1Offset +: PlatOwnerAuthSlot1Size]};
    // PLAT_OWNER_AUTH_SLOT2
    unused ^= ^{part_init_done[PlatOwnerAuthSlot2Idx],
                part_buf_data[PlatOwnerAuthSlot2Offset +: PlatOwnerAuthSlot2Size]};
    // PLAT_OWNER_AUTH_SLOT3
    unused ^= ^{part_init_done[PlatOwnerAuthSlot3Idx],
                part_buf_data[PlatOwnerAuthSlot3Offset +: PlatOwnerAuthSlot3Size]};
    // EXT_NVM
    unused ^= ^{part_init_done[ExtNvmIdx],
                part_buf_data[ExtNvmOffset +: ExtNvmSize]};
    // ROM_PATCH
    unused ^= ^{part_init_done[RomPatchIdx],
                part_buf_data[RomPatchOffset +: RomPatchSize]};
    // HW_CFG0
    valid &= part_init_done[HwCfg0Idx];
    otp_broadcast.hw_cfg0_data = otp_hw_cfg0_data_t'(part_buf_data[HwCfg0Offset +: (HwCfg0Size - 16)]);
    unused ^= ^part_buf_data[HwCfg0Offset + (HwCfg0Size - 16) +: 16];
    // HW_CFG1
    valid &= part_init_done[HwCfg1Idx];
    otp_broadcast.hw_cfg1_data = otp_hw_cfg1_data_t'(part_buf_data[HwCfg1Offset +: (HwCfg1Size - 16)]);
    unused ^= ^part_buf_data[HwCfg1Offset + (HwCfg1Size - 16) +: 16];
    // SECRET0
    unused ^= ^{part_init_done[Secret0Idx],
                part_buf_data[Secret0Offset +: Secret0Size]};
    // SECRET1
    unused ^= ^{part_init_done[Secret1Idx],
                part_buf_data[Secret1Offset +: Secret1Size]};
    // SECRET2
    unused ^= ^{part_init_done[Secret2Idx],
                part_buf_data[Secret2Offset +: Secret2Size]};
    // SECRET3
    unused ^= ^{part_init_done[Secret3Idx],
                part_buf_data[Secret3Offset +: Secret3Size]};
    // LIFE_CYCLE
    unused ^= ^{part_init_done[LifeCycleIdx],
                part_buf_data[LifeCycleOffset +: LifeCycleSize]};
    otp_broadcast.valid = lc_ctrl_pkg::lc_tx_bool_to_lc_tx(valid);
    return otp_broadcast;
  endfunction : named_broadcast_assign

  function automatic otp_keymgr_key_t named_keymgr_key_assign(
      logic [NumPart-1:0][ScrmblBlockWidth-1:0] part_digest,
      logic [$bits(PartInvDefault)/8-1:0][7:0] part_buf_data,
      lc_ctrl_pkg::lc_tx_t lc_seed_hw_rd_en);
    otp_keymgr_key_t otp_keymgr_key;
    logic valid, unused;
    unused = 1'b0;
    // For now we use a fixed struct type here so that the
    // interface to the keymgr remains stable. The type contains
    // a superset of all options, so we have to initialize it to '0 here.
    otp_keymgr_key = '0;
    // VENDOR_TEST
    unused ^= ^{part_digest[VendorTestIdx],
                part_buf_data[VendorTestOffset +: VendorTestSize]};
    // CREATOR_SW_CFG
    unused ^= ^{part_digest[CreatorSwCfgIdx],
                part_buf_data[CreatorSwCfgOffset +: CreatorSwCfgSize]};
    // OWNER_SW_CFG
    unused ^= ^{part_digest[OwnerSwCfgIdx],
                part_buf_data[OwnerSwCfgOffset +: OwnerSwCfgSize]};
    // OWNERSHIP_SLOT_STATE
    unused ^= ^{part_digest[OwnershipSlotStateIdx],
                part_buf_data[OwnershipSlotStateOffset +: OwnershipSlotStateSize]};
    // ROT_CREATOR_AUTH
    unused ^= ^{part_digest[RotCreatorAuthIdx],
                part_buf_data[RotCreatorAuthOffset +: RotCreatorAuthSize]};
    // ROT_OWNER_AUTH_SLOT0
    unused ^= ^{part_digest[RotOwnerAuthSlot0Idx],
                part_buf_data[RotOwnerAuthSlot0Offset +: RotOwnerAuthSlot0Size]};
    // ROT_OWNER_AUTH_SLOT1
    unused ^= ^{part_digest[RotOwnerAuthSlot1Idx],
                part_buf_data[RotOwnerAuthSlot1Offset +: RotOwnerAuthSlot1Size]};
    // PLAT_INTEG_AUTH_SLOT0
    unused ^= ^{part_digest[PlatIntegAuthSlot0Idx],
                part_buf_data[PlatIntegAuthSlot0Offset +: PlatIntegAuthSlot0Size]};
    // PLAT_INTEG_AUTH_SLOT1
    unused ^= ^{part_digest[PlatIntegAuthSlot1Idx],
                part_buf_data[PlatIntegAuthSlot1Offset +: PlatIntegAuthSlot1Size]};
    // PLAT_OWNER_AUTH_SLOT0
    unused ^= ^{part_digest[PlatOwnerAuthSlot0Idx],
                part_buf_data[PlatOwnerAuthSlot0Offset +: PlatOwnerAuthSlot0Size]};
    // PLAT_OWNER_AUTH_SLOT1
    unused ^= ^{part_digest[PlatOwnerAuthSlot1Idx],
                part_buf_data[PlatOwnerAuthSlot1Offset +: PlatOwnerAuthSlot1Size]};
    // PLAT_OWNER_AUTH_SLOT2
    unused ^= ^{part_digest[PlatOwnerAuthSlot2Idx],
                part_buf_data[PlatOwnerAuthSlot2Offset +: PlatOwnerAuthSlot2Size]};
    // PLAT_OWNER_AUTH_SLOT3
    unused ^= ^{part_digest[PlatOwnerAuthSlot3Idx],
                part_buf_data[PlatOwnerAuthSlot3Offset +: PlatOwnerAuthSlot3Size]};
    // EXT_NVM
    unused ^= ^{part_digest[ExtNvmIdx],
                part_buf_data[ExtNvmOffset +: ExtNvmSize]};
    // ROM_PATCH
    unused ^= ^{part_digest[RomPatchIdx],
                part_buf_data[RomPatchOffset +: RomPatchSize]};
    // HW_CFG0
    unused ^= ^{part_digest[HwCfg0Idx],
                part_buf_data[HwCfg0Offset +: HwCfg0Size]};
    // HW_CFG1
    unused ^= ^{part_digest[HwCfg1Idx],
                part_buf_data[HwCfg1Offset +: HwCfg1Size]};
    // SECRET0
    unused ^= ^{part_digest[Secret0Idx],
                part_buf_data[Secret0Offset +: Secret0Size]};
    // SECRET1
    unused ^= ^{part_digest[Secret1Idx],
                part_buf_data[Secret1Offset +: Secret1Size]};
    // SECRET2
    valid = (part_digest[Secret2Idx] != 0);
    unused ^= ^part_buf_data[RmaTokenOffset +: RmaTokenSize];
    otp_keymgr_key.creator_root_key_share0_valid = valid;
    if (lc_ctrl_pkg::lc_tx_test_true_strict(lc_seed_hw_rd_en)) begin
      otp_keymgr_key.creator_root_key_share0 =
          part_buf_data[CreatorRootKeyShare0Offset +: CreatorRootKeyShare0Size];
    end else begin
      otp_keymgr_key.creator_root_key_share0 =
          PartInvDefault[CreatorRootKeyShare0Offset*8 +: CreatorRootKeyShare0Size*8];
    end
    otp_keymgr_key.creator_root_key_share1_valid = valid;
    if (lc_ctrl_pkg::lc_tx_test_true_strict(lc_seed_hw_rd_en)) begin
      otp_keymgr_key.creator_root_key_share1 =
          part_buf_data[CreatorRootKeyShare1Offset +: CreatorRootKeyShare1Size];
    end else begin
      otp_keymgr_key.creator_root_key_share1 =
          PartInvDefault[CreatorRootKeyShare1Offset*8 +: CreatorRootKeyShare1Size*8];
    end
    otp_keymgr_key.creator_seed_valid = valid;
    if (lc_ctrl_pkg::lc_tx_test_true_strict(lc_seed_hw_rd_en)) begin
      otp_keymgr_key.creator_seed =
          part_buf_data[CreatorSeedOffset +: CreatorSeedSize];
    end else begin
      otp_keymgr_key.creator_seed =
          PartInvDefault[CreatorSeedOffset*8 +: CreatorSeedSize*8];
    end
    unused ^= ^part_buf_data[Secret2ZerOffset +: Secret2ZerSize];
    // This is not used since we consume the
    // ungated digest values from the part_digest array.
    unused ^= ^part_buf_data[Secret2DigestOffset +: Secret2DigestSize];
    // SECRET3
    valid = (part_digest[Secret3Idx] != 0);
    otp_keymgr_key.owner_seed_valid = valid;
    if (lc_ctrl_pkg::lc_tx_test_true_strict(lc_seed_hw_rd_en)) begin
      otp_keymgr_key.owner_seed =
          part_buf_data[OwnerSeedOffset +: OwnerSeedSize];
    end else begin
      otp_keymgr_key.owner_seed =
          PartInvDefault[OwnerSeedOffset*8 +: OwnerSeedSize*8];
    end
    unused ^= ^part_buf_data[Secret3ZerOffset +: Secret3ZerSize];
    // This is not used since we consume the
    // ungated digest values from the part_digest array.
    unused ^= ^part_buf_data[Secret3DigestOffset +: Secret3DigestSize];
    // LIFE_CYCLE
    unused ^= ^{part_digest[LifeCycleIdx],
                part_buf_data[LifeCycleOffset +: LifeCycleSize]};
    unused ^= valid;
    return otp_keymgr_key;
  endfunction : named_keymgr_key_assign

endpackage : otp_ctrl_part_pkg
