// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rstmgr.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"

#include "rstmgr_regs.h"  // Generated.

namespace dif_rstmgr_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Each;
using testing::Eq;
using testing::Test;

class RstmgrTest : public Test, public MmioTest {
 protected:
  dif_rstmgr_t rstmgr_ = {
      .params = {.base_addr = dev().region()},
  };
};

class InitTest : public RstmgrTest {};

TEST_F(InitTest, NullArgs) {
  dif_rstmgr_params_t params = {.base_addr = dev().region()};
  EXPECT_EQ(dif_rstmgr_init(params, nullptr), kDifRstmgrBadArg);
}

TEST_F(InitTest, Success) {
  dif_rstmgr_t rstmgr;
  dif_rstmgr_params_t params = {.base_addr = dev().region()};
  EXPECT_EQ(dif_rstmgr_init(params, &rstmgr), kDifRstmgrOk);
}

class ResetTest : public RstmgrTest {};

TEST_F(ResetTest, NullArgs) {
  EXPECT_EQ(dif_rstmgr_reset(nullptr), kDifRstmgrBadArg);
}

TEST_F(ResetTest, Success) {
  EXPECT_WRITE32(RSTMGR_RESET_INFO_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(RSTMGR_SW_RST_CTRL_N_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_EQ(dif_rstmgr_reset(&rstmgr_), kDifRstmgrOk);
}

class ResetLockTest : public RstmgrTest {};

TEST_F(ResetLockTest, NullArgs) {
  EXPECT_EQ(dif_rstmgr_reset_lock(nullptr, 0), kDifRstmgrBadArg);
}

TEST_F(ResetLockTest, BadPeripheral) {
  EXPECT_EQ(dif_rstmgr_reset_lock(&rstmgr_, RSTMGR_PARAM_NUMSWRESETS),
            kDifRstmgrBadArg);
}

TEST_F(ResetLockTest, Success) {
  for (uint32_t bit_index = 0; bit_index < RSTMGR_PARAM_NUMSWRESETS;
       ++bit_index) {
    // When bit is set to `0`, it means that the software reset for the
    // peripheral is locked. One by one lock every peripheral software reset,
    // by setting all bits high apart from the peripheral under test that is
    // indexed by `bit_index`.
    uint32_t bitfield = bitfield_bit32_write(
        std::numeric_limits<uint32_t>::max(), bit_index, false);
    EXPECT_WRITE32(RSTMGR_SW_RST_REGEN_REG_OFFSET, bitfield);

    EXPECT_EQ(dif_rstmgr_reset_lock(&rstmgr_, bit_index), kDifRstmgrOk);
  }
}

class ResetIsLockedTest : public RstmgrTest {};

TEST_F(ResetIsLockedTest, NullArgs) {
  bool is_locked;
  EXPECT_EQ(dif_rstmgr_reset_is_locked(nullptr, 0, nullptr), kDifRstmgrBadArg);
  EXPECT_EQ(dif_rstmgr_reset_is_locked(nullptr, 0, &is_locked),
            kDifRstmgrBadArg);
  EXPECT_EQ(dif_rstmgr_reset_is_locked(&rstmgr_, 0, nullptr), kDifRstmgrBadArg);
}

TEST_F(ResetIsLockedTest, BadPeripheral) {
  bool is_locked;
  EXPECT_EQ(dif_rstmgr_reset_is_locked(&rstmgr_, RSTMGR_PARAM_NUMSWRESETS,
                                       &is_locked),
            kDifRstmgrBadArg);
}

TEST_F(ResetIsLockedTest, Success) {
  for (uint32_t bit_index = 0; bit_index < RSTMGR_PARAM_NUMSWRESETS;
       ++bit_index) {
    // When bit is set to `0`, it means that the software reset for the
    // peripheral is locked. One by one we check every peripheral, by setting
    // all bits high apart from the peripheral under test that is indexed
    // by `bit_index`.
    uint32_t bit_locked = bitfield_bit32_write(
        std::numeric_limits<uint32_t>::max(), bit_index, false);
    EXPECT_READ32(RSTMGR_SW_RST_REGEN_REG_OFFSET, bit_locked);

    bool is_locked = false;
    EXPECT_EQ(dif_rstmgr_reset_is_locked(&rstmgr_, bit_index, &is_locked),
              kDifRstmgrOk);
    EXPECT_TRUE(is_locked);

    is_locked = true;
    EXPECT_READ32(RSTMGR_SW_RST_REGEN_REG_OFFSET, {{bit_index, true}});
    EXPECT_EQ(dif_rstmgr_reset_is_locked(&rstmgr_, bit_index, &is_locked),
              kDifRstmgrOk);
    EXPECT_FALSE(is_locked);
  }
}

class ResetCausesGetTest : public RstmgrTest {
 protected:
  ResetCausesGetTest() {
    // Make sure that the test is up-to-date with the implementation.
    uint32_t bitfield =
        bitfield_bit32_write(0, reset_info_reasons_.back(), true);
    EXPECT_EQ(bitfield, kDifRstmgrResetInfoLast);
  }

  const std::vector<uint32_t> reset_info_reasons_{
      RSTMGR_RESET_INFO_POR,
      RSTMGR_RESET_INFO_LOW_POWER_EXIT,
      RSTMGR_RESET_INFO_NDM_RESET,
      RSTMGR_RESET_INFO_HW_REQ,
  };
};

TEST_F(ResetCausesGetTest, NullArgs) {
  dif_rstmgr_reset_info_bitfield_t info;
  EXPECT_EQ(dif_rstmgr_reset_info_get(nullptr, nullptr), kDifRstmgrBadArg);
  EXPECT_EQ(dif_rstmgr_reset_info_get(nullptr, &info), kDifRstmgrBadArg);
  EXPECT_EQ(dif_rstmgr_reset_info_get(&rstmgr_, nullptr), kDifRstmgrBadArg);
}

TEST_F(ResetCausesGetTest, Success) {
  // Single reason expectations.
  for (auto reason : reset_info_reasons_) {
    uint32_t bitfield = bitfield_bit32_write(0, reason, true);
    EXPECT_READ32(RSTMGR_RESET_INFO_REG_OFFSET, bitfield);

    dif_rstmgr_reset_info_bitfield_t info;
    EXPECT_EQ(dif_rstmgr_reset_info_get(&rstmgr_, &info), kDifRstmgrOk);
    EXPECT_EQ(info & bitfield, info);
  }

  // The first and the last reset causes.
  EXPECT_READ32(RSTMGR_RESET_INFO_REG_OFFSET,
                {
                    {reset_info_reasons_.front(), true},
                    {reset_info_reasons_.back(), true},
                });

  dif_rstmgr_reset_info_bitfield_t info;
  EXPECT_EQ(dif_rstmgr_reset_info_get(&rstmgr_, &info), kDifRstmgrOk);
  EXPECT_EQ(info & (kDifRstmgrResetInfoPor | kDifRstmgrResetInfoLast), info);
}

class ResetCausesClearTest : public RstmgrTest {};

TEST_F(ResetCausesClearTest, NullArgs) {
  EXPECT_EQ(dif_rstmgr_reset_info_clear(nullptr), kDifRstmgrBadArg);
}

TEST_F(ResetCausesClearTest, Success) {
  EXPECT_WRITE32(RSTMGR_RESET_INFO_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_EQ(dif_rstmgr_reset_info_clear(&rstmgr_), kDifRstmgrOk);
}

class SoftwareResetTest : public RstmgrTest {};

TEST_F(SoftwareResetTest, NullArgs) {
  EXPECT_EQ(dif_rstmgr_software_reset(nullptr, 0, kDifRstmgrSoftwareReset),
            kDifRstmgrBadArg);
}

TEST_F(SoftwareResetTest, BadPeripheral) {
  EXPECT_EQ(dif_rstmgr_software_reset(&rstmgr_, RSTMGR_PARAM_NUMSWRESETS,
                                      kDifRstmgrSoftwareReset),
            kDifRstmgrBadArg);
}

TEST_F(SoftwareResetTest, SoftwareResetIsLocked) {
  for (uint32_t bit_index = 0; bit_index < RSTMGR_PARAM_NUMSWRESETS;
       ++bit_index) {
    // When bit is set to `0`, it means that the software reset for the
    // peripheral is locked. One by one we check every peripheral, by setting
    // all bits high apart from the peripheral under test that is indexed
    // by `bit_index`.
    uint32_t locked = bitfield_bit32_write(std::numeric_limits<uint32_t>::max(),
                                           bit_index, false);
    EXPECT_READ32(RSTMGR_SW_RST_REGEN_REG_OFFSET, locked);

    EXPECT_EQ(dif_rstmgr_software_reset(&rstmgr_, bit_index,
                                        kDifRstmgrSoftwareResetHold),
              kDifRstmgrSoftwareResetLocked);
  }
}

TEST_F(SoftwareResetTest, SuccessHold) {
  for (uint32_t bit_index = 0; bit_index < RSTMGR_PARAM_NUMSWRESETS;
       ++bit_index) {
    // Software reset is not locked for any of the supported peripherals.
    EXPECT_READ32(RSTMGR_SW_RST_REGEN_REG_OFFSET,
                  std::numeric_limits<uint32_t>::max());

    // Check that reset can be asserted for every supported peripheral.
    EXPECT_READ32(RSTMGR_SW_RST_CTRL_N_REG_OFFSET,
                  std::numeric_limits<uint32_t>::max());

    // When bit is set to `0`, it means that the peripheral is held in reset.
    // One by one hold every peripheral in reset, by setting all bits high apart
    // from the peripheral under test that is indexed by `bit_index`.
    uint32_t reset_hold = bitfield_bit32_write(
        std::numeric_limits<uint32_t>::max(), bit_index, false);
    EXPECT_WRITE32(RSTMGR_SW_RST_CTRL_N_REG_OFFSET, reset_hold);

    EXPECT_EQ(dif_rstmgr_software_reset(&rstmgr_, bit_index,
                                        kDifRstmgrSoftwareResetHold),
              kDifRstmgrOk);
  }
}

TEST_F(SoftwareResetTest, SuccessRelease) {
  for (uint32_t bit_index = 0; bit_index < RSTMGR_PARAM_NUMSWRESETS;
       ++bit_index) {
    // Software reset is not locked for any of the supported peripherals.
    EXPECT_READ32(RSTMGR_SW_RST_REGEN_REG_OFFSET,
                  std::numeric_limits<uint32_t>::max());

    // Check that reset can be de-asserted for every supported peripheral.
    EXPECT_READ32(RSTMGR_SW_RST_CTRL_N_REG_OFFSET, 0);
    EXPECT_WRITE32(RSTMGR_SW_RST_CTRL_N_REG_OFFSET, {{bit_index, true}});

    EXPECT_EQ(dif_rstmgr_software_reset(&rstmgr_, bit_index,
                                        kDifRstmgrSoftwareResetRelease),
              kDifRstmgrOk);
  }
}

TEST_F(SoftwareResetTest, SuccessReset) {
  for (uint32_t bit_index = 0; bit_index < RSTMGR_PARAM_NUMSWRESETS;
       ++bit_index) {
    // Software reset is not locked for any of the supported peripherals.
    EXPECT_READ32(RSTMGR_SW_RST_REGEN_REG_OFFSET,
                  std::numeric_limits<uint32_t>::max());

    // Check that reset can be asserted for every supported peripheral.
    EXPECT_READ32(RSTMGR_SW_RST_CTRL_N_REG_OFFSET,
                  std::numeric_limits<uint32_t>::max());

    // When bit is set to `0`, it means that the peripheral is held in reset.
    // One by one hold every peripheral in reset, by setting all bits high apart
    // from the peripheral under test that is indexed by `bit_index`.
    uint32_t reset_hold = bitfield_bit32_write(
        std::numeric_limits<uint32_t>::max(), bit_index, false);
    EXPECT_WRITE32(RSTMGR_SW_RST_CTRL_N_REG_OFFSET, reset_hold);

    // Check that reset can be de-asserted for every supported peripheral.
    EXPECT_READ32(RSTMGR_SW_RST_CTRL_N_REG_OFFSET, 0);
    EXPECT_WRITE32(RSTMGR_SW_RST_CTRL_N_REG_OFFSET, {{bit_index, true}});

    EXPECT_EQ(
        dif_rstmgr_software_reset(&rstmgr_, bit_index, kDifRstmgrSoftwareReset),
        kDifRstmgrOk);
  }
}

class SoftwareResetIsHeldTest : public RstmgrTest {};

TEST_F(SoftwareResetIsHeldTest, NullArgs) {
  EXPECT_EQ(dif_rstmgr_software_reset_is_held(nullptr, 0, nullptr),
            kDifRstmgrBadArg);

  bool asserted;
  EXPECT_EQ(dif_rstmgr_software_reset_is_held(nullptr, 0, &asserted),
            kDifRstmgrBadArg);

  EXPECT_EQ(dif_rstmgr_software_reset_is_held(&rstmgr_, 0, nullptr),
            kDifRstmgrBadArg);
}

TEST_F(SoftwareResetIsHeldTest, BadPeripheral) {
  bool asserted;
  EXPECT_EQ(dif_rstmgr_software_reset_is_held(
                &rstmgr_, RSTMGR_PARAM_NUMSWRESETS, &asserted),
            kDifRstmgrBadArg);
}

TEST_F(SoftwareResetIsHeldTest, Success) {
  for (uint32_t bit_index = 0; bit_index < RSTMGR_PARAM_NUMSWRESETS;
       ++bit_index) {
    uint32_t reset_is_held = bitfield_bit32_write(
        std::numeric_limits<uint32_t>::max(), bit_index, false);

    // Check in turn that every peripheral is held in software reset.
    EXPECT_READ32(RSTMGR_SW_RST_CTRL_N_REG_OFFSET, reset_is_held);

    bool asserted = false;
    EXPECT_EQ(dif_rstmgr_software_reset_is_held(&rstmgr_, bit_index, &asserted),
              kDifRstmgrOk);
    EXPECT_TRUE(asserted);

    // Check in turn that every peripheral is not held in software reset.
    EXPECT_READ32(RSTMGR_SW_RST_CTRL_N_REG_OFFSET, {{bit_index, true}});

    asserted = true;
    EXPECT_EQ(dif_rstmgr_software_reset_is_held(&rstmgr_, bit_index, &asserted),
              kDifRstmgrOk);
    EXPECT_FALSE(asserted);
  }
}

}  // namespace
}  // namespace dif_rstmgr_unittest
