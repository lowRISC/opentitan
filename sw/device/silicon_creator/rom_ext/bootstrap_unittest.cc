// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/bootstrap.h"

#include <stdint.h>
#include <vector>

#include "absl/types/optional.h"
#include "absl/types/span.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/bootstrap.h"
#include "sw/device/silicon_creator/lib/bootstrap_unittest_util.h"
#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/mock_spi_device.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/error_unittest_util.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "flash_ctrl_regs.h"
#include "hw/ip/otp_ctrl/data/otp_ctrl_regs.h"

// Custom equality operator for `flash_ctrl_cfg_t`. This must be defined outside
// the test's namespace for GTest to find it.
bool operator==(const flash_ctrl_cfg_t a, const flash_ctrl_cfg_t b) {
  return memcmp(&a, &b, sizeof(a)) == 0;
}

namespace rom_ext_bootstrap_unittest {
namespace {

using ::testing::_;
using ::testing::AtLeast;
using ::testing::Each;
using ::testing::Eq;
using ::testing::Return;

using bootstrap_unittest_util::ChipEraseCmd;
using bootstrap_unittest_util::PageProgramCmd;
using bootstrap_unittest_util::ResetCmd;
using bootstrap_unittest_util::SectorEraseCmd;

constexpr size_t kNumFlashCtrlMpRegions = 8;

/**
 * A collection of functions for simulating flash_ctrl operations on a chunk
 * of host memory.
 */
class FlashCtrlSim {
 private:
  // This struct defines the protection configuration for a single region.
  struct MpRegion {
    size_t page_offset = 0;
    size_t num_pages = 0;
    bool read_enabled = false;
    bool prog_enabled = false;
    bool erase_enabled = false;
    bool enabled = false;
  };

 public:
  // A human-readable byte value that represents the last operation performed on
  // an address in the simulated flash. This is intentionally written as a
  // regular enum rather than an enum class so implicit conversions and type
  // inferences on `Span<char>` work automatically.
  enum FlashByte : char {
    kDefault = 'd',
    kErased = 'e',
    kErasedVerified = 'v',
  };

  FlashCtrlSim() : memory_(flash_size(), FlashByte::kDefault) {}

  void BankErasePermsSet(hardened_bool_t enable) {
    bank_erase_perms_ = enable == kHardenedBoolTrue;
  }

  rom_error_t DataRegionProtect(flash_ctrl_region_index_t region,
                                uint32_t page_offset, uint32_t num_pages,
                                flash_ctrl_perms_t perms,
                                flash_ctrl_cfg_t cfg) {
    EXPECT_LT(region, kNumFlashCtrlMpRegions);
    EXPECT_LT(page_offset, FlashCtrlSim::num_pages());
    mp_regions_[region] = MpRegion{
        .page_offset = page_offset,
        .num_pages = num_pages,
        .read_enabled = perms.read == kMultiBitBool4True,
        .prog_enabled = perms.write == kMultiBitBool4True,
        .erase_enabled = perms.erase == kMultiBitBool4True,
        .enabled = true,
    };
    return kErrorOk;
  }

  rom_error_t DataErase(uint32_t addr, flash_ctrl_erase_type_t erase_type) {
    using ::testing::Eq;

    absl::Span<char> region;
    switch (erase_type) {
      case kFlashCtrlEraseTypeBank: {
        EXPECT_EQ(addr % bank_size(), 0);
        for (size_t i = 0; i < num_pages(); ++i) {
          uint32_t page_addr = addr + i * page_size();
          if (!ErasePageOk(page_addr)) {
            return kErrorFlashCtrlDataErase;
          }
        }
        region = GetFlash().subspan(addr, bank_size());
        break;
      }
      case kFlashCtrlEraseTypePage: {
        EXPECT_EQ(addr % page_size(), 0);
        if (!ErasePageOk(addr)) {
          return kErrorFlashCtrlDataErase;
        }
        region = GetFlash().subspan(addr, page_size());
        break;
      }
      default:
        ADD_FAILURE() << "DataErase is only implemented for banks and pages";
        return kErrorUnknown;
    }

    EXPECT_THAT(region, Each(Eq(FlashByte::kDefault)))
        << "DataErase should only see memory that hasn't been touched yet";
    memset(region.data(), FlashByte::kErased, region.size());

    return kErrorOk;
  }

  rom_error_t DataEraseVerify(uint32_t addr,
                              flash_ctrl_erase_type_t erase_type) {
    using ::testing::Eq;

    absl::Span<char> region;
    switch (erase_type) {
      case kFlashCtrlEraseTypeBank: {
        EXPECT_EQ(addr % bank_size(), 0);
        for (size_t i = 0; i < num_pages(); ++i) {
          uint32_t page_addr = addr + i * page_size();
          if (!ReadPageOk(page_addr)) {
            return kErrorFlashCtrlDataEraseVerify;
          }
        }
        region = GetFlash().subspan(addr, bank_size());
        break;
      }
      case kFlashCtrlEraseTypePage: {
        EXPECT_EQ(addr % page_size(), 0);
        region = GetFlash().subspan(addr, page_size());
        break;
      }
      default:
        ADD_FAILURE()
            << "DataEraseVerify is only implemented for banks and pages";
        return kErrorUnknown;
    }

    EXPECT_THAT(region, Each(Eq(FlashByte::kErased)))
        << "DataEraseVerify should only encounter that is already erased";
    memset(region.data(), FlashByte::kErasedVerified, region.size());
    return kErrorOk;
  }

  rom_error_t DataWrite(uint32_t addr, uint32_t word_count, const void *data) {
    if (!WritePageOk(addr)) {
      return kErrorFlashCtrlDataWrite;
    }

    const size_t num_bytes = word_count * sizeof(uint32_t);
    absl::Span<char> region = GetFlash().subspan(addr, num_bytes);
    EXPECT_EQ(region.size(), num_bytes);
    memcpy(region.data(), data, region.size());
    return kErrorOk;
  }

  static constexpr size_t flash_size() { return num_banks() * bank_size(); }

  absl::Span<char> GetFlash() { return absl::MakeSpan(memory_); }
  absl::Span<char> GetSlotA() { return GetFlash().subspan(0, bank_size()); }
  absl::Span<char> GetSlotB() { return GetFlash().subspan(bank_size()); }

  absl::Span<char> GetRomExtSlotA() {
    return GetSlotA().subspan(0, rom_ext_size());
  }

  absl::Span<char> GetRomExtSlotB() {
    return GetSlotB().subspan(0, rom_ext_size());
  }

 private:
  static constexpr size_t num_banks() { return FLASH_CTRL_PARAM_REG_NUM_BANKS; }
  static constexpr size_t bank_size() {
    return FLASH_CTRL_PARAM_BYTES_PER_BANK;
  }
  static constexpr size_t page_size() {
    return FLASH_CTRL_PARAM_BYTES_PER_PAGE;
  }
  static constexpr size_t num_pages() {
    constexpr size_t kFlashSize = bank_size() * num_banks();
    static_assert(kFlashSize % page_size() == 0,
                  "Flash size must be divisible by page size");
    return kFlashSize / page_size();
  }
  static constexpr size_t rom_ext_size() { return CHIP_ROM_EXT_SIZE_MAX; }

  // Finds the first enabled region that covers the given address. If no regions
  // cover the address, returns `absl::nullopt`.
  absl::optional<MpRegion> FindMpRegion(uint32_t addr) const {
    const size_t page = addr / page_size();
    for (const MpRegion &region : mp_regions_) {
      if (region.enabled && region.page_offset <= page &&
          page < region.page_offset + region.num_pages) {
        return region;
      }
    }
    return absl::nullopt;
  }
  // Returns true iff memory protection rules allow this address to be erased.
  // If there is no matching rule, it returns the the last flash-wide
  // erasability configured with `flash_ctrl_bank_erase_perms_set()`.
  bool ErasePageOk(uint32_t addr) const {
    absl::optional<MpRegion> region = FindMpRegion(addr);
    return region ? region->erase_enabled : bank_erase_perms_;
  }
  // Returns true iff memory protection rules allow this address to be read.
  // If there is no matching rule, it returns the the last flash-wide
  // readability configured with `flash_ctrl_bank_erase_perms_set()`.
  bool ReadPageOk(uint32_t addr) const {
    absl::optional<MpRegion> region = FindMpRegion(addr);
    return region ? region->read_enabled : bank_erase_perms_;
  }
  // Returns true iff memory protection rules allow programming pages at this
  // address. Otherwise, returns false.
  bool WritePageOk(uint32_t addr) const {
    absl::optional<MpRegion> region = FindMpRegion(addr);
    return region ? region->prog_enabled : false;
  }

  bool bank_erase_perms_ = false;

  MpRegion mp_regions_[kNumFlashCtrlMpRegions]{};

  std::vector<char> memory_;
};

/**
 * A test fixture with convenience methods for setting expectations related to
 * ROM_EXT bootstrap.
 */
class RomExtBootstrapTest : public bootstrap_unittest_util::BootstrapTest {
 protected:
  /**
   * Sets an expectation that `otp_read32()` will be called with the address
   * of ROM_EXT_BOOTSTRAP_EN.
   *
   * @param value The value to return from the mocked `otp_read32()`.
   */
  void SetRomExtBootstrapEnabledInOtp(uint32_t value) {
    EXPECT_CALL(otp_,
                read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_EXT_BOOTSTRAP_EN_OFFSET))
        .WillOnce(Return(value));
  }

  /**
   * Sets an expectation that `rstmgr_reason_get()` will be called.
   *
   * @param value The value to return from the mocked `rstmgr_reason_get()`.
   */
  void SetResetReason(uint32_t value) {
    EXPECT_CALL(rstmgr_, ReasonGet()).WillOnce(Return(value));
  }

  /**
   * Delegates some flash_ctrl operations to `FlashCtrlSim`. This enables tests
   * to write expectations in terms of the contents of flash.
   */
  void DelegateToFlashCtrlSim() {
    using ::testing::_;

    ON_CALL(flash_ctrl_, DataRegionProtect(_, _, _, _, _))
        .WillByDefault([&](flash_ctrl_region_index_t region,
                           uint32_t page_offset, uint32_t num_pages,
                           flash_ctrl_perms_t perms, flash_ctrl_cfg_t cfg) {
          return flash_ctrl_sim_.DataRegionProtect(region, page_offset,
                                                   num_pages, perms, cfg);
        });
    ON_CALL(flash_ctrl_, BankErasePermsSet(_))
        .WillByDefault([&](hardened_bool_t enable) {
          return flash_ctrl_sim_.BankErasePermsSet(enable);
        });
    ON_CALL(flash_ctrl_, DataErase(_, _))
        .WillByDefault([&](uint32_t addr, flash_ctrl_erase_type_t type) {
          return flash_ctrl_sim_.DataErase(addr, type);
        });
    ON_CALL(flash_ctrl_, DataEraseVerify(_, _))
        .WillByDefault([&](uint32_t addr, flash_ctrl_erase_type_t type) {
          return flash_ctrl_sim_.DataEraseVerify(addr, type);
        });
    ON_CALL(flash_ctrl_, DataWrite(_, _, _))
        .WillByDefault(
            [&](uint32_t addr, uint32_t word_count, const void *data) {
              return flash_ctrl_sim_.DataWrite(addr, word_count, data);
            });
  }

  void ExpectRomExtSlotA(FlashCtrlSim::FlashByte byte) {
    const absl::Span<char> rom_ext_slot_a = flash_ctrl_sim_.GetRomExtSlotA();
    EXPECT_FALSE(rom_ext_slot_a.empty());
    EXPECT_THAT(rom_ext_slot_a, Each(Eq(byte)));
  }

  void ExpectRomExtSlotB(FlashCtrlSim::FlashByte byte) {
    const absl::Span<char> rom_ext_slot_b = flash_ctrl_sim_.GetRomExtSlotB();
    EXPECT_FALSE(rom_ext_slot_b.empty());
    EXPECT_THAT(rom_ext_slot_b, Each(Eq(byte)));
  }

  void ExpectSuffixSlotA(FlashCtrlSim::FlashByte byte) {
    const absl::Span<char> slot_a_suffix = flash_ctrl_sim_.GetSlotA().subspan(
        flash_ctrl_sim_.GetRomExtSlotA().size());
    EXPECT_FALSE(slot_a_suffix.empty());
    EXPECT_THAT(slot_a_suffix, Each(Eq(byte)));
  }

  void ExpectSuffixSlotB(FlashCtrlSim::FlashByte byte) {
    const absl::Span<char> slot_b_suffix = flash_ctrl_sim_.GetSlotB().subspan(
        flash_ctrl_sim_.GetRomExtSlotB().size());
    EXPECT_THAT(slot_b_suffix, Each(Eq(byte)));
  }

  FlashCtrlSim flash_ctrl_sim_;

  const flash_ctrl_cfg_t kFlashCtrlCfg = {
      .scrambling = kMultiBitBool4True,
      .ecc = kMultiBitBool4True,
      .he = kMultiBitBool4True,
  };
};

// ROM_EXT bootstrap is disabled when the OTP value is `kHardenedBoolFalse`.
TEST_F(RomExtBootstrapTest, BootstrapDisabledByOtp) {
  SetRomExtBootstrapEnabledInOtp(kHardenedBoolFalse);
  EXPECT_EQ(rom_ext_bootstrap_enabled(), kHardenedBoolFalse);
}

// Bootstrap is disabled when the OTP value is an invalid hardened bool.
TEST_F(RomExtBootstrapTest, BootstrapDisabledByOtpGlitch) {
  constexpr hardened_bool_t kHardenedBoolMiddle =
      static_cast<hardened_bool_t>(kHardenedBoolFalse + 1);
  static_assert(kHardenedBoolMiddle != kHardenedBoolTrue &&
                    kHardenedBoolMiddle != kHardenedBoolFalse,
                "kHardenedBoolMiddle should be invalid");
  SetRomExtBootstrapEnabledInOtp(kHardenedBoolMiddle);
  EXPECT_EQ(rom_ext_bootstrap_enabled(), kHardenedBoolFalse);
}

// Bootstrap is disabled when the OTP value is `kHardenedBoolTrue` and the reset
// reason is zero.
TEST_F(RomExtBootstrapTest, BootstrapDisabledByResetReasonZero) {
  SetRomExtBootstrapEnabledInOtp(kHardenedBoolTrue);
  SetResetReason(0);
  EXPECT_EQ(rom_ext_bootstrap_enabled(), kHardenedBoolFalse);
}

// Bootstrap is disabled when the OTP value is hardened true, but the reset
// reason is something other than PoR.
TEST_F(RomExtBootstrapTest, BootstrapDisabledByResetReasonLowPowerExit) {
  SetRomExtBootstrapEnabledInOtp(kHardenedBoolTrue);
  SetResetReason(1 << kRstmgrReasonLowPowerExit);
  EXPECT_EQ(rom_ext_bootstrap_enabled(), kHardenedBoolFalse);
}

// Bootstrap is enabled when the OTP value is hardened true and the reset reason
// is PoR.
TEST_F(RomExtBootstrapTest, BootstrapEnabledByResetReasonPor) {
  SetRomExtBootstrapEnabledInOtp(kHardenedBoolTrue);
  SetResetReason(1 << kRstmgrReasonPowerOn);
  EXPECT_EQ(rom_ext_bootstrap_enabled(), kHardenedBoolTrue);
}

// Bootstrap is enabled when the OTP value is hardened true and the reset reason
// contains PoR and other values.
TEST_F(RomExtBootstrapTest, BootstrapEnabledByResetReasonPorEtc) {
  SetRomExtBootstrapEnabledInOtp(kHardenedBoolTrue);
  SetResetReason(1 << kRstmgrReasonPowerOn | 1 << kRstmgrReasonSoftwareRequest);
  EXPECT_EQ(rom_ext_bootstrap_enabled(), kHardenedBoolTrue);
}

// Verify that `rom_ext_bootstrap()` fails with the appropriate status when
// bootstrap is disabled in OTP.
TEST_F(RomExtBootstrapTest, BootstrapDisabled) {
  SetRomExtBootstrapEnabledInOtp(kHardenedBoolFalse);
  EXPECT_EQ(rom_ext_bootstrap(), kErrorBootstrapDisabledRomExt);
}

// A minimal ROM_EXT bootstrap session erases both flash slots except for the
// ROM_EXT region in each slot.
TEST_F(RomExtBootstrapTest, BootstrapEnabledSimple) {
  using FlashByte = FlashCtrlSim::FlashByte;

  // This test will forward calls to flash_ctrl functions to
  // `flash_ctrl_sim_`, enabling us to set expectations in terms of the
  // contents of the flash.
  DelegateToFlashCtrlSim();

  SetRomExtBootstrapEnabledInOtp(kHardenedBoolTrue);
  SetResetReason(1 << kRstmgrReasonPowerOn | 1 << kRstmgrReasonSoftwareRequest);

  EXPECT_CALL(flash_ctrl_, DataDefaultCfgGet()).WillOnce(Return(kFlashCtrlCfg));

  EXPECT_CALL(flash_ctrl_, DataRegionProtect(_, _, _, _, kFlashCtrlCfg))
      .Times(3);

  EXPECT_CALL(spi_device_, Init());

  // bootstrap_handle_erase
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  EXPECT_CALL(flash_ctrl_, BankErasePermsSet(kHardenedBoolTrue));
  EXPECT_CALL(flash_ctrl_, DataErase(testing::_, kFlashCtrlEraseTypePage))
      .Times(AtLeast(1));
  EXPECT_CALL(flash_ctrl_, BankErasePermsSet(kHardenedBoolFalse));

  // bootstrap_handle_erase_verify
  EXPECT_CALL(flash_ctrl_, DataEraseVerify(testing::_, kFlashCtrlEraseTypePage))
      .Times(AtLeast(1));
  EXPECT_CALL(spi_device_, FlashStatusClear());

  // bootstrap_handle_program
  ExpectSpiCmd(ResetCmd());
  EXPECT_CALL(rstmgr_, Reset());

  EXPECT_THAT(flash_ctrl_sim_.GetFlash(), Each(Eq(FlashByte::kDefault)))
      << "Before rom_ext_bootstrap(), flash should be unmodified.";

  // Host-specific behavior causes bootstrap to return `kErrorUnknown` on RESET.
  EXPECT_EQ(rom_ext_bootstrap(), kErrorUnknown);

  ExpectRomExtSlotA(FlashByte::kDefault);
  ExpectSuffixSlotA(FlashByte::kErasedVerified);
  ExpectRomExtSlotB(FlashByte::kDefault);
  ExpectSuffixSlotB(FlashByte::kErasedVerified);
}

// ROM_EXT bootstrap ignores every non-erase command it receives until it has
// performed a chip erase.
TEST_F(RomExtBootstrapTest, BootstrapEnabledJunkBeforeEraseCmd) {
  using FlashByte = FlashCtrlSim::FlashByte;

  // This test will forward calls to flash_ctrl functions to
  // `flash_ctrl_sim_`, enabling us to set expectations in terms of the
  // contents of the flash.
  DelegateToFlashCtrlSim();

  SetRomExtBootstrapEnabledInOtp(kHardenedBoolTrue);
  SetResetReason(1 << kRstmgrReasonPowerOn | 1 << kRstmgrReasonSoftwareRequest);

  EXPECT_CALL(flash_ctrl_, DataDefaultCfgGet()).WillOnce(Return(kFlashCtrlCfg));

  EXPECT_CALL(flash_ctrl_, DataRegionProtect(_, _, _, _, kFlashCtrlCfg))
      .Times(3);

  EXPECT_CALL(spi_device_, Init());

  // bootstrap_handle_erase

  // Non-erase command PAGE_PROGRAM is ignored.
  ExpectSpiCmd(PageProgramCmd(0x0, 123));
  ExpectSpiFlashStatusGet(true);
  EXPECT_CALL(spi_device_, FlashStatusClear());

  // Non-erase command RESET is ignored.
  ExpectSpiCmd(ResetCmd());
  ExpectSpiFlashStatusGet(true);
  EXPECT_CALL(spi_device_, FlashStatusClear());

  // CHIP_ERASE command kicks off the bootstrap procedure.
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  EXPECT_CALL(flash_ctrl_, BankErasePermsSet(kHardenedBoolTrue));
  EXPECT_CALL(flash_ctrl_, DataErase(testing::_, kFlashCtrlEraseTypePage))
      .Times(AtLeast(1));
  EXPECT_CALL(flash_ctrl_, BankErasePermsSet(kHardenedBoolFalse));

  // bootstrap_handle_erase_verify
  EXPECT_CALL(flash_ctrl_, DataEraseVerify(testing::_, kFlashCtrlEraseTypePage))
      .Times(AtLeast(1));
  EXPECT_CALL(spi_device_, FlashStatusClear());

  // bootstrap_handle_program
  ExpectSpiCmd(ResetCmd());
  EXPECT_CALL(rstmgr_, Reset());

  EXPECT_THAT(flash_ctrl_sim_.GetFlash(), Each(Eq(FlashByte::kDefault)))
      << "Before rom_ext_bootstrap(), flash should be unmodified.";

  // Host-specific behavior causes bootstrap to return `kErrorUnknown` on RESET.
  EXPECT_EQ(rom_ext_bootstrap(), kErrorUnknown);

  ExpectRomExtSlotA(FlashByte::kDefault);
  ExpectSuffixSlotA(FlashByte::kErasedVerified);
  ExpectRomExtSlotB(FlashByte::kDefault);
  ExpectSuffixSlotB(FlashByte::kErasedVerified);
}

// Bootstrap refuses to act on SECTOR_ERASE commands that would erase part of
// ROM_EXT in slot A.
TEST_F(RomExtBootstrapTest, BootstrapProtectsRomExtWithSectorEraseInSlotA) {
  using FlashByte = FlashCtrlSim::FlashByte;

  // This test will forward calls to flash_ctrl functions to
  // `flash_ctrl_sim_`, enabling us to set expectations in terms of the
  // contents of the flash.
  DelegateToFlashCtrlSim();

  SetRomExtBootstrapEnabledInOtp(kHardenedBoolTrue);
  SetResetReason(1 << kRstmgrReasonPowerOn | 1 << kRstmgrReasonSoftwareRequest);

  EXPECT_CALL(flash_ctrl_, DataDefaultCfgGet()).WillOnce(Return(kFlashCtrlCfg));

  EXPECT_CALL(flash_ctrl_, DataRegionProtect(_, _, _, _, kFlashCtrlCfg))
      .Times(3);

  EXPECT_CALL(spi_device_, Init());

  // bootstrap_handle_erase

  // CHIP_ERASE command kicks off the bootstrap procedure.
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  EXPECT_CALL(flash_ctrl_, BankErasePermsSet(kHardenedBoolTrue));
  EXPECT_CALL(flash_ctrl_, DataErase(testing::_, kFlashCtrlEraseTypePage))
      .Times(AtLeast(1));
  EXPECT_CALL(flash_ctrl_, BankErasePermsSet(kHardenedBoolFalse));

  // bootstrap_handle_erase_verify
  EXPECT_CALL(flash_ctrl_, DataEraseVerify(testing::_, kFlashCtrlEraseTypePage))
      .Times(AtLeast(1));
  EXPECT_CALL(spi_device_, FlashStatusClear());

  // bootstrap_handle_program
  ExpectSpiCmd(SectorEraseCmd(0x0));
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlEraseEnable();
  EXPECT_CALL(flash_ctrl_, DataErase(testing::_, kFlashCtrlEraseTypePage))
      .Times(2);
  ExpectFlashCtrlAllDisable();

  EXPECT_THAT(flash_ctrl_sim_.GetFlash(), Each(Eq(FlashByte::kDefault)))
      << "Before rom_ext_bootstrap(), flash should be unmodified.";

  EXPECT_EQ(rom_ext_bootstrap(), kErrorFlashCtrlDataErase);

  // The ROM_EXT region in slot A should have been untouched by initial chip
  // erase. Later, during the programming loop, the SECTOR_ERASE command should
  // have been caught by the memory protection rules.
  ExpectRomExtSlotA(FlashByte::kDefault);
  ExpectSuffixSlotA(FlashByte::kErasedVerified);
  ExpectRomExtSlotB(FlashByte::kDefault);
  ExpectSuffixSlotB(FlashByte::kErasedVerified);
}

// Bootstrap refuses to act on SECTOR_ERASE commands that would erase any part
// of ROM_EXT in slot B.
TEST_F(RomExtBootstrapTest, BootstrapProtectsRomExtWithSectorEraseInSlotB) {
  using FlashByte = FlashCtrlSim::FlashByte;

  // This test will forward calls to flash_ctrl functions to
  // `flash_ctrl_sim_`, enabling us to set expectations in terms of the
  // contents of the flash.
  DelegateToFlashCtrlSim();

  SetRomExtBootstrapEnabledInOtp(kHardenedBoolTrue);
  SetResetReason(1 << kRstmgrReasonPowerOn | 1 << kRstmgrReasonSoftwareRequest);

  EXPECT_CALL(flash_ctrl_, DataDefaultCfgGet()).WillOnce(Return(kFlashCtrlCfg));

  EXPECT_CALL(flash_ctrl_, DataRegionProtect(_, _, _, _, kFlashCtrlCfg))
      .Times(3);

  EXPECT_CALL(spi_device_, Init());

  // bootstrap_handle_erase

  // CHIP_ERASE command kicks off the bootstrap procedure.
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  EXPECT_CALL(flash_ctrl_, BankErasePermsSet(kHardenedBoolTrue));
  EXPECT_CALL(flash_ctrl_, DataErase(testing::_, kFlashCtrlEraseTypePage))
      .Times(AtLeast(1));
  EXPECT_CALL(flash_ctrl_, BankErasePermsSet(kHardenedBoolFalse));

  // bootstrap_handle_erase_verify
  EXPECT_CALL(flash_ctrl_, DataEraseVerify(testing::_, kFlashCtrlEraseTypePage))
      .Times(AtLeast(1));
  EXPECT_CALL(spi_device_, FlashStatusClear());

  // bootstrap_handle_program
  ExpectSpiCmd(SectorEraseCmd(FLASH_CTRL_PARAM_BYTES_PER_BANK +
                              CHIP_ROM_EXT_SIZE_MAX / 2));
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlEraseEnable();
  EXPECT_CALL(flash_ctrl_, DataErase(testing::_, kFlashCtrlEraseTypePage))
      .Times(2);
  ExpectFlashCtrlAllDisable();

  EXPECT_THAT(flash_ctrl_sim_.GetFlash(), Each(Eq(FlashByte::kDefault)))
      << "Before rom_ext_bootstrap(), flash should be unmodified.";

  // Host-specific behavior causes bootstrap to return `kErrorUnknown` on RESET.
  EXPECT_EQ(rom_ext_bootstrap(), kErrorFlashCtrlDataErase);

  ExpectRomExtSlotA(FlashByte::kDefault);
  ExpectSuffixSlotA(FlashByte::kErasedVerified);

  // The ROM_EXT region in slot B should have been untouched by initial chip
  // erase. Later, during the programming loop, the SECTOR_ERASE command should
  // have been caught by the memory protection rules rather than erasing two
  // pages in the middle of the ROM_EXT.
  ExpectRomExtSlotB(FlashByte::kDefault);
  ExpectSuffixSlotB(FlashByte::kErasedVerified);
}

// Bootstrap refuses to act on PAGE_PROGRAM commands that would overwrite any
// part of ROM_EXT in slot A.
TEST_F(RomExtBootstrapTest, BootstrapProtectsRomExtWithPageProgramInSlotA) {
  using FlashByte = FlashCtrlSim::FlashByte;

  // This test will forward calls to flash_ctrl functions to
  // `flash_ctrl_sim_`, enabling us to set expectations in terms of the
  // contents of the flash.
  DelegateToFlashCtrlSim();

  SetRomExtBootstrapEnabledInOtp(kHardenedBoolTrue);
  SetResetReason(1 << kRstmgrReasonPowerOn | 1 << kRstmgrReasonSoftwareRequest);

  EXPECT_CALL(flash_ctrl_, DataDefaultCfgGet()).WillOnce(Return(kFlashCtrlCfg));

  EXPECT_CALL(flash_ctrl_, DataRegionProtect(_, _, _, _, kFlashCtrlCfg))
      .Times(3);

  EXPECT_CALL(spi_device_, Init());

  // bootstrap_handle_erase
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  EXPECT_CALL(flash_ctrl_, BankErasePermsSet(kHardenedBoolTrue));
  EXPECT_CALL(flash_ctrl_, DataErase(testing::_, kFlashCtrlEraseTypePage))
      .Times(AtLeast(1));
  EXPECT_CALL(flash_ctrl_, BankErasePermsSet(kHardenedBoolFalse));

  // bootstrap_handle_erase_verify
  EXPECT_CALL(flash_ctrl_, DataEraseVerify(testing::_, kFlashCtrlEraseTypePage))
      .Times(AtLeast(1));
  EXPECT_CALL(spi_device_, FlashStatusClear());

  // bootstrap_handle_program
  ExpectSpiCmd(PageProgramCmd(CHIP_ROM_EXT_SIZE_MAX / 2, 16));
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlWriteEnable();
  EXPECT_CALL(flash_ctrl_, DataWrite(testing::_, 4, testing::_));
  ExpectFlashCtrlAllDisable();

  EXPECT_THAT(flash_ctrl_sim_.GetFlash(), Each(Eq(FlashByte::kDefault)))
      << "Before rom_ext_bootstrap(), flash should be unmodified.";

  // Host-specific behavior causes bootstrap to return `kErrorUnknown` on RESET.
  EXPECT_EQ(rom_ext_bootstrap(), kErrorFlashCtrlDataWrite);

  // The ROM_EXT region in slot A should have been untouched by initial chip
  // erase. Later, during the programming loop, the PAGE_PROGRAM command should
  // have been caught by the memory protection rules rather than erasing 16
  // words in the middle of the ROM_EXT.
  ExpectRomExtSlotA(FlashByte::kDefault);
  ExpectSuffixSlotA(FlashByte::kErasedVerified);
  ExpectRomExtSlotB(FlashByte::kDefault);
  ExpectSuffixSlotB(FlashByte::kErasedVerified);
}

// Bootstrap refuses to act on PAGE_PROGRAM commands that would overwrite any
// part of ROM_EXT in slot B.
TEST_F(RomExtBootstrapTest, BootstrapProtectsRomExtWithPageProgramInSlotB) {
  using FlashByte = FlashCtrlSim::FlashByte;

  // This test will forward calls to flash_ctrl functions to
  // `flash_ctrl_sim_`, enabling us to set expectations in terms of the
  // contents of the flash.
  DelegateToFlashCtrlSim();

  SetRomExtBootstrapEnabledInOtp(kHardenedBoolTrue);
  SetResetReason(1 << kRstmgrReasonPowerOn | 1 << kRstmgrReasonSoftwareRequest);

  EXPECT_CALL(flash_ctrl_, DataDefaultCfgGet()).WillOnce(Return(kFlashCtrlCfg));

  EXPECT_CALL(flash_ctrl_, DataRegionProtect(_, _, _, _, kFlashCtrlCfg))
      .Times(3);

  EXPECT_CALL(spi_device_, Init());

  // bootstrap_handle_erase
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  EXPECT_CALL(flash_ctrl_, BankErasePermsSet(kHardenedBoolTrue));
  EXPECT_CALL(flash_ctrl_, DataErase(testing::_, kFlashCtrlEraseTypePage))
      .Times(AtLeast(1));
  EXPECT_CALL(flash_ctrl_, BankErasePermsSet(kHardenedBoolFalse));

  // bootstrap_handle_erase_verify
  EXPECT_CALL(flash_ctrl_, DataEraseVerify(testing::_, kFlashCtrlEraseTypePage))
      .Times(AtLeast(1));
  EXPECT_CALL(spi_device_, FlashStatusClear());

  // bootstrap_handle_program
  ExpectSpiCmd(PageProgramCmd(FLASH_CTRL_PARAM_BYTES_PER_BANK, 16));
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlWriteEnable();
  EXPECT_CALL(flash_ctrl_, DataWrite(testing::_, 4, testing::_));
  ExpectFlashCtrlAllDisable();

  EXPECT_THAT(flash_ctrl_sim_.GetFlash(), Each(Eq(FlashByte::kDefault)))
      << "Before rom_ext_bootstrap(), flash should be unmodified.";

  // Host-specific behavior causes bootstrap to return `kErrorUnknown` on RESET.
  EXPECT_EQ(rom_ext_bootstrap(), kErrorFlashCtrlDataWrite);

  // The ROM_EXT region in slot B should have been untouched by initial chip
  // erase. Later, during the programming loop, the PAGE_PROGRAM command should
  // have been caught by the memory protection rules rather than erasing 16
  // words at the front of the ROM_EXT.
  ExpectRomExtSlotA(FlashByte::kDefault);
  ExpectSuffixSlotA(FlashByte::kErasedVerified);
  ExpectRomExtSlotB(FlashByte::kDefault);
  ExpectSuffixSlotB(FlashByte::kErasedVerified);
}

}  // namespace
}  // namespace rom_ext_bootstrap_unittest
