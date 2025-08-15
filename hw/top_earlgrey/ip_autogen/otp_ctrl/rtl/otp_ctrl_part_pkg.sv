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

  parameter int NumScrmblKeys = 3;
  parameter int NumDigestSets = 4;

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
    Secret2Key
  } key_sel_e;

  typedef enum logic [ConstSelWidth-1:0] {
    CnstyDigest,
    FlashDataKey,
    FlashAddrKey,
    SramDataKey
  } digest_sel_e;

  // SEC_CM: SECRET.MEM.SCRAMBLE
  parameter key_array_t RndCnstKey = {
    128'h85A9E830BC059BA9286D6E2856A05CC3,
    128'hEFFA6D736C5EFF49AE7B70F9C46E5A62,
    128'h3BA121C5E097DDEB7768B4C666E9C3DA
  };

  // SEC_CM: PART.MEM.DIGEST
  // Note: digest set 0 is used for computing the partition digests. Constants at
  // higher indices are used to compute the scrambling keys.
  parameter digest_const_array_t RndCnstDigestConst = {
    128'h4A22D4B78FE0266FBEE3958332F2939B,
    128'hD60822E1FAEC5C7290C7F21F6224F027,
    128'h277195FC471E4B26B6641214B61D1B43,
    128'hE95F517CB98955B4D5A89AA9109294A
  };

  parameter digest_iv_array_t RndCnstDigestIV = {
    64'hF98C48B1F9377284,
    64'hB7474D640F8A7F5,
    64'hE048B657396B4B83,
    64'hBEAD91D5FA4E0915
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
      offset:           11'd0,
      size:             64,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b0,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b0
    },
    // CREATOR_SW_CFG
    '{
      variant:          Unbuffered,
      offset:           11'd64,
      size:             368,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b0
    },
    // OWNER_SW_CFG
    '{
      variant:          Unbuffered,
      offset:           11'd432,
      size:             712,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b0
    },
    // ROT_CREATOR_AUTH_CODESIGN
    '{
      variant:          Unbuffered,
      offset:           11'd1144,
      size:             472,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b0
    },
    // ROT_CREATOR_AUTH_STATE
    '{
      variant:          Unbuffered,
      offset:           11'd1616,
      size:             40,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b1,
      hw_digest:        1'b0,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b0
    },
    // HW_CFG0
    '{
      variant:          Buffered,
      offset:           11'd1656,
      size:             72,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b0,
      hw_digest:        1'b1,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b0
    },
    // HW_CFG1
    '{
      variant:          Buffered,
      offset:           11'd1728,
      size:             16,
      key_sel:          key_sel_e'('0),
      secret:           1'b0,
      sw_digest:        1'b0,
      hw_digest:        1'b1,
      write_lock:       1'b1,
      read_lock:        1'b0,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b0
    },
    // SECRET0
    '{
      variant:          Buffered,
      offset:           11'd1744,
      size:             40,
      key_sel:          Secret0Key,
      secret:           1'b1,
      sw_digest:        1'b0,
      hw_digest:        1'b1,
      write_lock:       1'b1,
      read_lock:        1'b1,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b0
    },
    // SECRET1
    '{
      variant:          Buffered,
      offset:           11'd1784,
      size:             88,
      key_sel:          Secret1Key,
      secret:           1'b1,
      sw_digest:        1'b0,
      hw_digest:        1'b1,
      write_lock:       1'b1,
      read_lock:        1'b1,
      integrity:        1'b1,
      iskeymgr_creator: 1'b0,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b0
    },
    // SECRET2
    '{
      variant:          Buffered,
      offset:           11'd1872,
      size:             88,
      key_sel:          Secret2Key,
      secret:           1'b1,
      sw_digest:        1'b0,
      hw_digest:        1'b1,
      write_lock:       1'b1,
      read_lock:        1'b1,
      integrity:        1'b1,
      iskeymgr_creator: 1'b1,
      iskeymgr_owner:   1'b0,
      zeroizable:       1'b0
    },
    // LIFE_CYCLE
    '{
      variant:          LifeCycle,
      offset:           11'd1960,
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
    RotCreatorAuthCodesignIdx,
    RotCreatorAuthStateIdx,
    HwCfg0Idx,
    HwCfg1Idx,
    Secret0Idx,
    Secret1Idx,
    Secret2Idx,
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
    manuf_state: 256'hDF3888886BD10DC67ABB319BDA0529AE40119A3C6E63CDF358840E458E4029A6,
    device_id: 256'h63B9485A3856C417CF7A50A9A91EF7F7B3A5B4421F462370FFF698183664DC7E
  };
  typedef struct packed {
    logic [39:0] unallocated;
    prim_mubi_pkg::mubi8_t dis_rv_dm_late_debug;
    prim_mubi_pkg::mubi8_t en_csrng_sw_app_read;
    prim_mubi_pkg::mubi8_t en_sram_ifetch;
  } otp_hw_cfg1_data_t;

  // default value used for intermodule
  parameter otp_hw_cfg1_data_t OTP_HW_CFG1_DATA_DEFAULT = '{
    unallocated: 40'h0,
    dis_rv_dm_late_debug: prim_mubi_pkg::mubi8_t'(8'h69),
    en_csrng_sw_app_read: prim_mubi_pkg::mubi8_t'(8'h69),
    en_sram_ifetch: prim_mubi_pkg::mubi8_t'(8'h69)
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
  parameter logic [16383:0] PartInvDefault = 16384'({
    // LIFE_CYCLE default
    704'({
      // LC_STATE
      320'h93B61DE417B9FB339605F051E74379CBCC6596C7174EBA643E725E464F593C87A445C3C29F71A256,
      // LC_TRANSITION_CNT
      384'hA0D1E90E8C9FDDFA01E46311FD36D95401136C663A36C3E3E817E760B27AE937BFCDF15A3429452A851B80674A2B6FBE
    }),
    // SECRET2 default
    704'({
      // SECRET2_DIGEST
      64'h8CBBAD02BB4CA928,
      // CREATOR_ROOT_KEY_SHARE1
      256'hD68C96F0B3D1FEED688098A43C33459F0279FC51CC7C626E315FD2B871D88819,
      // CREATOR_ROOT_KEY_SHARE0
      256'hD0BAC511D08ECE0E2C0DBDDEDF7A854D5E58D0AA97A0F8F6D3D58610F4851667,
      // RMA_TOKEN
      128'h94CD3DED94B578192A4D8B51F5D41C8A
    }),
    // SECRET1 default
    704'({
      // SECRET1_DIGEST
      64'hC469C593E5DC0DA8,
      // SRAM_DATA_KEY_SEED
      128'hE00E9680BD9B70291C752824C7DDC896,
      // FLASH_DATA_KEY_SEED
      256'h105733EAA3880C5A234729143F97B62A55D0320379A0D260426D99D374E699CA,
      // FLASH_ADDR_KEY_SEED
      256'hDBC827839FE2DCC27E17D06B5D4E0DDDDBB9844327F20FB5D396D1CE085BDC31
    }),
    // SECRET0 default
    320'({
      // SECRET0_DIGEST
      64'hBE193854E9CA60A0,
      // TEST_EXIT_TOKEN
      128'h711D135F59A50322B6711DB6F5D40A37,
      // TEST_UNLOCK_TOKEN
      128'hB5AC1F53D00A08C3B28B5C0FEE5F4C02
    }),
    // HW_CFG1 default
    128'({
      // HW_CFG1_DIGEST
      64'hBBF4A76885E754F2,
      // DIS_RV_DM_LATE_DEBUG
      40'h0, // unallocated 5 bytes
      8'h69,
      // EN_CSRNG_SW_APP_READ
      8'h69,
      // EN_SRAM_IFETCH
      8'h69
    }),
    // HW_CFG0 default
    576'({
      // HW_CFG0_DIGEST
      64'hF87BED95CFBA3727,
      // MANUF_STATE
      256'hDF3888886BD10DC67ABB319BDA0529AE40119A3C6E63CDF358840E458E4029A6,
      // DEVICE_ID
      256'h63B9485A3856C417CF7A50A9A91EF7F7B3A5B4421F462370FFF698183664DC7E
    }),
    // ROT_CREATOR_AUTH_STATE default
    320'({
      // ROT_CREATOR_AUTH_STATE_DIGEST
      64'h20440F25BB053FB5,
      // ROT_CREATOR_AUTH_STATE_SPX_KEY3
      32'h0,
      // ROT_CREATOR_AUTH_STATE_SPX_KEY2
      32'h0,
      // ROT_CREATOR_AUTH_STATE_SPX_KEY1
      32'h0,
      // ROT_CREATOR_AUTH_STATE_SPX_KEY0
      32'h0,
      // ROT_CREATOR_AUTH_STATE_ECDSA_KEY3
      32'h0,
      // ROT_CREATOR_AUTH_STATE_ECDSA_KEY2
      32'h0,
      // ROT_CREATOR_AUTH_STATE_ECDSA_KEY1
      32'h0,
      // ROT_CREATOR_AUTH_STATE_ECDSA_KEY0
      32'h0
    }),
    // ROT_CREATOR_AUTH_CODESIGN default
    3776'({
      // ROT_CREATOR_AUTH_CODESIGN_DIGEST
      64'h15F164D7930C9D19,
      // ROT_CREATOR_AUTH_CODESIGN_BLOCK_SHA2_256_HASH
      256'h0,
      // ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG3
      32'h0,
      // ROT_CREATOR_AUTH_CODESIGN_SPX_KEY3
      256'h0,
      // ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE3
      32'h0,
      // ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG2
      32'h0,
      // ROT_CREATOR_AUTH_CODESIGN_SPX_KEY2
      256'h0,
      // ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE2
      32'h0,
      // ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG1
      32'h0,
      // ROT_CREATOR_AUTH_CODESIGN_SPX_KEY1
      256'h0,
      // ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE1
      32'h0,
      // ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG0
      32'h0,
      // ROT_CREATOR_AUTH_CODESIGN_SPX_KEY0
      256'h0,
      // ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE0
      32'h0,
      // ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY3
      512'h0,
      // ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE3
      32'h0,
      // ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY2
      512'h0,
      // ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE2
      32'h0,
      // ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY1
      512'h0,
      // ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE1
      32'h0,
      // ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY0
      512'h0,
      // ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE0
      32'h0
    }),
    // OWNER_SW_CFG default
    5696'({
      // OWNER_SW_CFG_DIGEST
      64'hE29749216775E8A5,
      // OWNER_SW_CFG_RESERVED
      96'h0, // unallocated 12 bytes
      1024'h0,
      // OWNER_SW_CFG_ROM_FLASH_ECC_EXC_HANDLER_EN
      32'h0,
      // OWNER_SW_CFG_ROM_BANNER_EN
      32'h0,
      // OWNER_SW_CFG_ROM_RESET_REASON_CHECK_VALUE
      32'h0,
      // OWNER_SW_CFG_ROM_PRESERVE_RESET_REASON_EN
      32'h0,
      // OWNER_SW_CFG_ROM_SRAM_READBACK_EN
      32'h0,
      // OWNER_SW_CFG_ROM_SENSOR_CTRL_ALERT_CFG
      96'h0,
      // OWNER_SW_CFG_ROM_EXT_BOOTSTRAP_EN
      32'h0,
      // OWNER_SW_CFG_ROM_RSTMGR_INFO_EN
      32'h0,
      // OWNER_SW_CFG_MANUF_STATE
      32'h0,
      // OWNER_SW_CFG_ROM_KEYMGR_OTP_MEAS_EN
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
      2560'h0,
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
    2944'({
      // CREATOR_SW_CFG_DIGEST
      64'h340A5B93BB19342,
      // CREATOR_SW_CFG_RESERVED
      96'h0, // unallocated 12 bytes
      256'h0,
      // CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_SHA256_HASH
      256'h0,
      // CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_LENGTH
      32'h0,
      // CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_START_OFFSET
      32'h0,
      // CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN
      32'h0,
      // CREATOR_SW_CFG_SRAM_KEY_RENEW_EN
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
      // CREATOR_SW_CFG_SIGVERIFY_SPX_EN
      32'h0,
      // CREATOR_SW_CFG_ROM_EXT_SKU
      32'h0,
      // CREATOR_SW_CFG_AST_INIT_EN
      32'h0,
      // CREATOR_SW_CFG_AST_CFG
      1248'h0
    }),
    // VENDOR_TEST default
    512'({
      // VENDOR_TEST_DIGEST
      64'h4947DD361344767A,
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
    hw2reg.rot_creator_auth_codesign_digest = part_digest[RotCreatorAuthCodesignIdx];
    hw2reg.rot_creator_auth_state_digest = part_digest[RotCreatorAuthStateIdx];
    hw2reg.hw_cfg0_digest = part_digest[HwCfg0Idx];
    hw2reg.hw_cfg1_digest = part_digest[HwCfg1Idx];
    hw2reg.secret0_digest = part_digest[Secret0Idx];
    hw2reg.secret1_digest = part_digest[Secret1Idx];
    hw2reg.secret2_digest = part_digest[Secret2Idx];
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
    // ROT_CREATOR_AUTH_CODESIGN
    if (!reg2hw.rot_creator_auth_codesign_read_lock) begin
      part_access_pre[RotCreatorAuthCodesignIdx].read_lock = prim_mubi_pkg::MuBi8True;
    end
    // ROT_CREATOR_AUTH_STATE
    if (!reg2hw.rot_creator_auth_state_read_lock) begin
      part_access_pre[RotCreatorAuthStateIdx].read_lock = prim_mubi_pkg::MuBi8True;
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
    // ROT_CREATOR_AUTH_CODESIGN
    unused ^= ^{part_init_done[RotCreatorAuthCodesignIdx],
                part_buf_data[RotCreatorAuthCodesignOffset +: RotCreatorAuthCodesignSize]};
    // ROT_CREATOR_AUTH_STATE
    unused ^= ^{part_init_done[RotCreatorAuthStateIdx],
                part_buf_data[RotCreatorAuthStateOffset +: RotCreatorAuthStateSize]};
    // HW_CFG0
    valid &= part_init_done[HwCfg0Idx];
    otp_broadcast.hw_cfg0_data = otp_hw_cfg0_data_t'(part_buf_data[HwCfg0Offset +: (HwCfg0Size - 8)]);
    unused ^= ^part_buf_data[HwCfg0Offset + (HwCfg0Size - 8) +: 8];
    // HW_CFG1
    valid &= part_init_done[HwCfg1Idx];
    otp_broadcast.hw_cfg1_data = otp_hw_cfg1_data_t'(part_buf_data[HwCfg1Offset +: (HwCfg1Size - 8)]);
    unused ^= ^part_buf_data[HwCfg1Offset + (HwCfg1Size - 8) +: 8];
    // SECRET0
    unused ^= ^{part_init_done[Secret0Idx],
                part_buf_data[Secret0Offset +: Secret0Size]};
    // SECRET1
    unused ^= ^{part_init_done[Secret1Idx],
                part_buf_data[Secret1Offset +: Secret1Size]};
    // SECRET2
    unused ^= ^{part_init_done[Secret2Idx],
                part_buf_data[Secret2Offset +: Secret2Size]};
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
    // ROT_CREATOR_AUTH_CODESIGN
    unused ^= ^{part_digest[RotCreatorAuthCodesignIdx],
                part_buf_data[RotCreatorAuthCodesignOffset +: RotCreatorAuthCodesignSize]};
    // ROT_CREATOR_AUTH_STATE
    unused ^= ^{part_digest[RotCreatorAuthStateIdx],
                part_buf_data[RotCreatorAuthStateOffset +: RotCreatorAuthStateSize]};
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
    // This is not used since we consume the
    // ungated digest values from the part_digest array.
    unused ^= ^part_buf_data[Secret2DigestOffset +: Secret2DigestSize];
    // LIFE_CYCLE
    unused ^= ^{part_digest[LifeCycleIdx],
                part_buf_data[LifeCycleOffset +: LifeCycleSize]};
    unused ^= valid;
    return otp_keymgr_key;
  endfunction : named_keymgr_key_assign

endpackage : otp_ctrl_part_pkg
