// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use bitflags::bitflags;

use bindgen::dif;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u32)]
#[non_exhaustive]
pub enum OtpCtrlReg {
    IntrState = dif::OTP_CTRL_INTR_STATE_REG_OFFSET,
    IntrEnable = dif::OTP_CTRL_INTR_ENABLE_REG_OFFSET,
    IntrTest = dif::OTP_CTRL_INTR_TEST_REG_OFFSET,
    AlertTest = dif::OTP_CTRL_ALERT_TEST_REG_OFFSET,
    Status = dif::OTP_CTRL_STATUS_REG_OFFSET,
    ErrCode = dif::OTP_CTRL_ERR_CODE_REG_OFFSET,
    DirectAccessRegwen = dif::OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET,
    DirectAccessCmd = dif::OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET,
    DirectAccessAddress = dif::OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET,
    DirectAccessWdata0 = dif::OTP_CTRL_DIRECT_ACCESS_WDATA_0_REG_OFFSET,
    DirectAccessWdata1 = dif::OTP_CTRL_DIRECT_ACCESS_WDATA_1_REG_OFFSET,
    DirectAccessRdata0 = dif::OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET,
    DirectAccessRdata1 = dif::OTP_CTRL_DIRECT_ACCESS_RDATA_1_REG_OFFSET,
    CheckTriggerRegwen = dif::OTP_CTRL_CHECK_TRIGGER_REGWEN_REG_OFFSET,
    CheckTrigger = dif::OTP_CTRL_CHECK_TRIGGER_REG_OFFSET,
    CheckRegwen = dif::OTP_CTRL_CHECK_REGWEN_REG_OFFSET,
    CheckTimeout = dif::OTP_CTRL_CHECK_TIMEOUT_REG_OFFSET,
    IntegrityCheckPeriod = dif::OTP_CTRL_INTEGRITY_CHECK_PERIOD_REG_OFFSET,
    ConsistencyCheckPeriod = dif::OTP_CTRL_CONSISTENCY_CHECK_PERIOD_REG_OFFSET,
    VendorTestReadLock = dif::OTP_CTRL_VENDOR_TEST_READ_LOCK_REG_OFFSET,
    CreatorSwCfgReadLock = dif::OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_REG_OFFSET,
    OwnerSwCfgReadLock = dif::OTP_CTRL_OWNER_SW_CFG_READ_LOCK_REG_OFFSET,
    VendorTestDigest0 = dif::OTP_CTRL_VENDOR_TEST_DIGEST_0_REG_OFFSET,
    VendorTestDigest1 = dif::OTP_CTRL_VENDOR_TEST_DIGEST_1_REG_OFFSET,
    CreatorSwCfgDigest0 = dif::OTP_CTRL_CREATOR_SW_CFG_DIGEST_0_REG_OFFSET,
    CreatorSwCfgDigest1 = dif::OTP_CTRL_CREATOR_SW_CFG_DIGEST_1_REG_OFFSET,
    OwnerSwCfgDigest0 = dif::OTP_CTRL_OWNER_SW_CFG_DIGEST_0_REG_OFFSET,
    OwnerSwCfgDigest1 = dif::OTP_CTRL_OWNER_SW_CFG_DIGEST_1_REG_OFFSET,
    HwCfgDigest0 = dif::OTP_CTRL_HW_CFG_DIGEST_0_REG_OFFSET,
    HwCfgDigest1 = dif::OTP_CTRL_HW_CFG_DIGEST_1_REG_OFFSET,
    Secret0Digest0 = dif::OTP_CTRL_SECRET0_DIGEST_0_REG_OFFSET,
    Secret0Digest1 = dif::OTP_CTRL_SECRET0_DIGEST_1_REG_OFFSET,
    Secret1Digest0 = dif::OTP_CTRL_SECRET1_DIGEST_0_REG_OFFSET,
    Secret1Digest1 = dif::OTP_CTRL_SECRET1_DIGEST_1_REG_OFFSET,
    Secret2Digest0 = dif::OTP_CTRL_SECRET2_DIGEST_0_REG_OFFSET,
    Secret2Digest1 = dif::OTP_CTRL_SECRET2_DIGEST_1_REG_OFFSET,
    SwCfgWindow = dif::OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET,
}

bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct DirectAccessCmd: u32 {
        const DIGEST = 0b1 << dif::OTP_CTRL_DIRECT_ACCESS_CMD_DIGEST_BIT;
        const RD     = 0b1 << dif::OTP_CTRL_DIRECT_ACCESS_CMD_RD_BIT;
        const WR     = 0b1 << dif::OTP_CTRL_DIRECT_ACCESS_CMD_WR_BIT;
    }
}

bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct OtpCtrlStatus: u32 {
        const BUS_INTEG_ERROR       = 0b1 << dif::OTP_CTRL_STATUS_BUS_INTEG_ERROR_BIT;
        const CHECK_PENDING         = 0b1 << dif::OTP_CTRL_STATUS_CHECK_PENDING_BIT;
        const CREATOR_SW_CFG_ERROR  = 0b1 << dif::OTP_CTRL_STATUS_CREATOR_SW_CFG_ERROR_BIT;
        const DAI_ERROR             = 0b1 << dif::OTP_CTRL_STATUS_DAI_ERROR_BIT;
        const DAI_IDLE              = 0b1 << dif::OTP_CTRL_STATUS_DAI_IDLE_BIT;
        const HW_CFG_ERROR          = 0b1 << dif::OTP_CTRL_STATUS_HW_CFG_ERROR_BIT;
        const KEY_DERIV_FSM_ERROR   = 0b1 << dif::OTP_CTRL_STATUS_KEY_DERIV_FSM_ERROR_BIT;
        const LCI_ERROR             = 0b1 << dif::OTP_CTRL_STATUS_LCI_ERROR_BIT;
        const LFSR_FSM_ERROR        = 0b1 << dif::OTP_CTRL_STATUS_LFSR_FSM_ERROR_BIT;
        const LIFE_CYCLE_ERROR      = 0b1 << dif::OTP_CTRL_STATUS_LIFE_CYCLE_ERROR_BIT;
        const OWNER_SW_CFG_ERROR    = 0b1 << dif::OTP_CTRL_STATUS_OWNER_SW_CFG_ERROR_BIT;
        const SCRAMBLING_FSM_ERROR  = 0b1 << dif::OTP_CTRL_STATUS_SCRAMBLING_FSM_ERROR_BIT;
        const SECRET0_ERROR         = 0b1 << dif::OTP_CTRL_STATUS_SECRET0_ERROR_BIT;
        const SECRET1_ERROR         = 0b1 << dif::OTP_CTRL_STATUS_SECRET1_ERROR_BIT;
        const SECRET2_ERROR         = 0b1 << dif::OTP_CTRL_STATUS_SECRET2_ERROR_BIT;
        const TIMEOUT_ERROR         = 0b1 << dif::OTP_CTRL_STATUS_TIMEOUT_ERROR_BIT;
        const VENDOR_TEST_ERROR     = 0b1 << dif::OTP_CTRL_STATUS_VENDOR_TEST_ERROR_BIT;

        const ERRORS =
            Self::BUS_INTEG_ERROR.bits() |
            Self::CREATOR_SW_CFG_ERROR.bits() |
            Self::DAI_ERROR.bits() |
            Self::HW_CFG_ERROR.bits() |
            Self::KEY_DERIV_FSM_ERROR.bits() |
            Self::LCI_ERROR.bits() |
            Self::LFSR_FSM_ERROR.bits() |
            Self::LIFE_CYCLE_ERROR.bits() |
            Self::OWNER_SW_CFG_ERROR.bits() |
            Self::SCRAMBLING_FSM_ERROR.bits() |
            Self::SECRET0_ERROR.bits() |
            Self::SECRET1_ERROR.bits() |
            Self::SECRET2_ERROR.bits() |
            Self::TIMEOUT_ERROR.bits() |
            Self::VENDOR_TEST_ERROR.bits();
    }
}

pub struct Partition {
    /// Granularity of accesses at this address.
    pub access_granule: Granularity,

    /// Starting address of this partition within the OTP in bytes.
    pub byte_addr: u32,

    /// Digest MMAP for this partition.
    ///
    /// Must be accessed with 64-bit granularity, regardless of this
    /// partition's `access_granule`.
    pub digest: OtpParamMmap,
}

impl Partition {
    // TODO: Take granularities from the `.hjson` instead of hardcoding.
    pub const CREATOR_SW_CFG: Self = Self {
        access_granule: Granularity::B32,
        byte_addr: dif::OTP_CTRL_PARAM_CREATOR_SW_CFG_OFFSET,
        digest: OtpParamMmap {
            byte_addr: dif::OTP_CTRL_PARAM_CREATOR_SW_CFG_DIGEST_OFFSET,
            size: dif::OTP_CTRL_PARAM_CREATOR_SW_CFG_DIGEST_SIZE,
        },
    };

    pub const OWNER_SW_CFG: Self = Self {
        access_granule: Granularity::B32,
        byte_addr: dif::OTP_CTRL_PARAM_OWNER_SW_CFG_OFFSET,
        digest: OtpParamMmap {
            byte_addr: dif::OTP_CTRL_PARAM_OWNER_SW_CFG_DIGEST_OFFSET,
            size: dif::OTP_CTRL_PARAM_OWNER_SW_CFG_DIGEST_SIZE,
        },
    };

    pub const HW_CFG: Self = Self {
        access_granule: Granularity::B32,
        byte_addr: dif::OTP_CTRL_PARAM_HW_CFG_OFFSET,
        digest: OtpParamMmap {
            byte_addr: dif::OTP_CTRL_PARAM_HW_CFG_DIGEST_OFFSET,
            size: dif::OTP_CTRL_PARAM_HW_CFG_DIGEST_SIZE,
        },
    };

    pub const SECRET0: Self = Self {
        access_granule: Granularity::B64,
        byte_addr: dif::OTP_CTRL_PARAM_SECRET0_OFFSET,
        digest: OtpParamMmap {
            byte_addr: dif::OTP_CTRL_PARAM_SECRET0_DIGEST_OFFSET,
            size: dif::OTP_CTRL_PARAM_SECRET0_DIGEST_SIZE,
        },
    };

    pub const SECRET1: Self = Self {
        access_granule: Granularity::B64,
        byte_addr: dif::OTP_CTRL_PARAM_SECRET1_OFFSET,
        digest: OtpParamMmap {
            byte_addr: dif::OTP_CTRL_PARAM_SECRET1_DIGEST_OFFSET,
            size: dif::OTP_CTRL_PARAM_SECRET1_DIGEST_SIZE,
        },
    };

    pub const SECRET2: Self = Self {
        access_granule: Granularity::B64,
        byte_addr: dif::OTP_CTRL_PARAM_SECRET2_OFFSET,
        digest: OtpParamMmap {
            byte_addr: dif::OTP_CTRL_PARAM_SECRET2_DIGEST_OFFSET,
            size: dif::OTP_CTRL_PARAM_SECRET2_DIGEST_SIZE,
        },
    };
}

/// Granularities of memory accesses.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Granularity {
    /// 32-bit.
    B32,
    /// 64-bit.
    B64,
}

/// Represents an OTP parameter's mapping in the "direct access memory".
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OtpParamMmap {
    /// Byte address of this OTP parameter.
    pub byte_addr: u32,

    /// Size in bytes.
    pub size: u32,
}

/// Parameters accessible via Direct Access Interface (DAI).
///
/// The `CREATOR_SW_CFG` and `OWNER_SW_CFG` partitions are omitted for brevity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DaiParam {
    // HW_CFG
    DeviceId,
    ManufState,
    EnSramIfetch,
    EnCsrngSwAppRead,
    EnEntropySrcFwRead,
    EnEntropySrcFwOver,
    // SECRET0
    TestUnlockToken,
    TestExitToken,
    // SECRET1
    FlashAddrKeySeed,
    FlashDataKeySeed,
    SramDataKeySeed,
    // SECRET2
    RmaToken,
    CreatorRootKeyShare0,
    CreatorRootKeyShare1,
}

impl DaiParam {
    // These constants should be generated by `reggen` in the future.
    pub const DEVICE_ID: OtpParamMmap = OtpParamMmap {
        byte_addr: dif::OTP_CTRL_PARAM_DEVICE_ID_OFFSET,
        size: dif::OTP_CTRL_PARAM_DEVICE_ID_SIZE,
    };
    pub const MANUF_STATE: OtpParamMmap = OtpParamMmap {
        byte_addr: dif::OTP_CTRL_PARAM_MANUF_STATE_OFFSET,
        size: dif::OTP_CTRL_PARAM_MANUF_STATE_SIZE,
    };
    pub const EN_SRAM_IFETCH: OtpParamMmap = OtpParamMmap {
        byte_addr: dif::OTP_CTRL_PARAM_EN_SRAM_IFETCH_OFFSET,
        size: dif::OTP_CTRL_PARAM_EN_SRAM_IFETCH_SIZE,
    };
    pub const EN_CSRNG_SW_APP_READ: OtpParamMmap = OtpParamMmap {
        byte_addr: dif::OTP_CTRL_PARAM_EN_CSRNG_SW_APP_READ_OFFSET,
        size: dif::OTP_CTRL_PARAM_EN_CSRNG_SW_APP_READ_SIZE,
    };
    pub const EN_ENTROPY_SRC_FW_READ: OtpParamMmap = OtpParamMmap {
        byte_addr: dif::OTP_CTRL_PARAM_EN_ENTROPY_SRC_FW_READ_OFFSET,
        size: dif::OTP_CTRL_PARAM_EN_ENTROPY_SRC_FW_READ_SIZE,
    };
    pub const EN_ENTROPY_SRC_FW_OVER: OtpParamMmap = OtpParamMmap {
        byte_addr: dif::OTP_CTRL_PARAM_EN_ENTROPY_SRC_FW_OVER_OFFSET,
        size: dif::OTP_CTRL_PARAM_EN_ENTROPY_SRC_FW_OVER_SIZE,
    };
    pub const TEST_UNLOCK_TOKEN: OtpParamMmap = OtpParamMmap {
        byte_addr: dif::OTP_CTRL_PARAM_TEST_UNLOCK_TOKEN_OFFSET,
        size: dif::OTP_CTRL_PARAM_TEST_UNLOCK_TOKEN_SIZE,
    };
    pub const TEST_EXIT_TOKEN: OtpParamMmap = OtpParamMmap {
        byte_addr: dif::OTP_CTRL_PARAM_TEST_EXIT_TOKEN_OFFSET,
        size: dif::OTP_CTRL_PARAM_TEST_EXIT_TOKEN_SIZE,
    };
    pub const FLASH_ADDR_KEY_SEED: OtpParamMmap = OtpParamMmap {
        byte_addr: dif::OTP_CTRL_PARAM_FLASH_ADDR_KEY_SEED_OFFSET,
        size: dif::OTP_CTRL_PARAM_FLASH_ADDR_KEY_SEED_SIZE,
    };
    pub const FLASH_DATA_KEY_SEED: OtpParamMmap = OtpParamMmap {
        byte_addr: dif::OTP_CTRL_PARAM_FLASH_DATA_KEY_SEED_OFFSET,
        size: dif::OTP_CTRL_PARAM_FLASH_DATA_KEY_SEED_SIZE,
    };
    pub const SRAM_DATA_KEY_SEED: OtpParamMmap = OtpParamMmap {
        byte_addr: dif::OTP_CTRL_PARAM_SRAM_DATA_KEY_SEED_OFFSET,
        size: dif::OTP_CTRL_PARAM_SRAM_DATA_KEY_SEED_SIZE,
    };
    pub const RMA_TOKEN: OtpParamMmap = OtpParamMmap {
        byte_addr: dif::OTP_CTRL_PARAM_RMA_TOKEN_OFFSET,
        size: dif::OTP_CTRL_PARAM_RMA_TOKEN_SIZE,
    };
    pub const CREATOR_ROOT_KEY_SHARE0: OtpParamMmap = OtpParamMmap {
        byte_addr: dif::OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_OFFSET,
        size: dif::OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_SIZE,
    };
    pub const CREATOR_ROOT_KEY_SHARE1: OtpParamMmap = OtpParamMmap {
        byte_addr: dif::OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE1_OFFSET,
        size: dif::OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE1_SIZE,
    };

    /// Returns the mmap'd field of this DAI parameter.
    pub const fn mmap(&self) -> OtpParamMmap {
        match self {
            Self::DeviceId => Self::DEVICE_ID,
            Self::ManufState => Self::MANUF_STATE,
            Self::EnSramIfetch => Self::EN_SRAM_IFETCH,
            Self::EnCsrngSwAppRead => Self::EN_CSRNG_SW_APP_READ,
            Self::EnEntropySrcFwRead => Self::EN_ENTROPY_SRC_FW_READ,
            Self::EnEntropySrcFwOver => Self::EN_ENTROPY_SRC_FW_OVER,
            Self::TestUnlockToken => Self::TEST_UNLOCK_TOKEN,
            Self::TestExitToken => Self::TEST_EXIT_TOKEN,
            Self::FlashAddrKeySeed => Self::FLASH_ADDR_KEY_SEED,
            Self::FlashDataKeySeed => Self::FLASH_DATA_KEY_SEED,
            Self::SramDataKeySeed => Self::SRAM_DATA_KEY_SEED,
            Self::RmaToken => Self::RMA_TOKEN,
            Self::CreatorRootKeyShare0 => Self::CREATOR_ROOT_KEY_SHARE0,
            Self::CreatorRootKeyShare1 => Self::CREATOR_ROOT_KEY_SHARE1,
        }
    }

    /// Returns the partition that this DAI parameter belongs to.
    pub const fn partition(&self) -> Partition {
        match self {
            Self::DeviceId => Partition::HW_CFG,
            Self::ManufState => Partition::HW_CFG,
            Self::EnSramIfetch => Partition::HW_CFG,
            Self::EnCsrngSwAppRead => Partition::HW_CFG,
            Self::EnEntropySrcFwRead => Partition::HW_CFG,
            Self::EnEntropySrcFwOver => Partition::HW_CFG,
            Self::TestUnlockToken => Partition::SECRET0,
            Self::TestExitToken => Partition::SECRET0,
            Self::FlashAddrKeySeed => Partition::SECRET1,
            Self::FlashDataKeySeed => Partition::SECRET1,
            Self::SramDataKeySeed => Partition::SECRET1,
            Self::RmaToken => Partition::SECRET2,
            Self::CreatorRootKeyShare0 => Partition::SECRET2,
            Self::CreatorRootKeyShare1 => Partition::SECRET2,
        }
    }
}
