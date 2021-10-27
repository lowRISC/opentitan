// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_sram_ctrl.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sram_ctrl_regs.h"  // Generated.

namespace dif_sram_ctrl_autogen_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Test;

class SramCtrlTest : public Test, public MmioTest {
 protected:
  dif_sram_ctrl_t sram_ctrl_ = {.base_addr = dev().region()};
};

class RequestNewKeyTest : public SramCtrlTest {};

TEST_F(RequestNewKeyTest, NullArgs) {
  EXPECT_EQ(dif_sram_ctrl_request_new_key(nullptr), kDifBadArg);
}

TEST_F(RequestNewKeyTest, Locked) {
  EXPECT_READ32(SRAM_CTRL_CTRL_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_sram_ctrl_request_new_key(&sram_ctrl_), kDifLocked);
}

TEST_F(RequestNewKeyTest, Success) {
  EXPECT_READ32(SRAM_CTRL_CTRL_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(SRAM_CTRL_CTRL_REG_OFFSET,
                 {{SRAM_CTRL_CTRL_RENEW_SCR_KEY_BIT, true},
                  {SRAM_CTRL_CTRL_INIT_BIT, false}});
  EXPECT_EQ(dif_sram_ctrl_request_new_key(&sram_ctrl_), kDifOk);
}

class GetStatusTest : public SramCtrlTest {};

TEST_F(GetStatusTest, NullArgs) {
  dif_sram_ctrl_status_bitfield_t status;
  EXPECT_EQ(dif_sram_ctrl_get_status(&sram_ctrl_, nullptr), kDifBadArg);
  EXPECT_EQ(dif_sram_ctrl_get_status(nullptr, &status), kDifBadArg);
  EXPECT_EQ(dif_sram_ctrl_get_status(nullptr, nullptr), kDifBadArg);
}

TEST_F(GetStatusTest, SuccessSome) {
  EXPECT_READ32(SRAM_CTRL_STATUS_REG_OFFSET, 0xA5A5A5A5);

  dif_sram_ctrl_status_bitfield_t status = 0;
  EXPECT_EQ(dif_sram_ctrl_get_status(&sram_ctrl_, &status), kDifOk);
  EXPECT_EQ(status, 0xA5A5A5A5);
}

TEST_F(GetStatusTest, SuccessAll) {
  EXPECT_READ32(SRAM_CTRL_STATUS_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());

  dif_sram_ctrl_status_bitfield_t status = 0;
  EXPECT_EQ(dif_sram_ctrl_get_status(&sram_ctrl_, &status), kDifOk);
  EXPECT_EQ(status, std::numeric_limits<uint32_t>::max());
}

TEST_F(GetStatusTest, SuccessNone) {
  EXPECT_READ32(SRAM_CTRL_STATUS_REG_OFFSET, 0);

  dif_sram_ctrl_status_bitfield_t status = std::numeric_limits<uint32_t>::max();
  EXPECT_EQ(dif_sram_ctrl_get_status(&sram_ctrl_, &status), kDifOk);
  EXPECT_EQ(status, 0);
}

class ExecGetEnabledTest : public SramCtrlTest {};

TEST_F(ExecGetEnabledTest, NullArgs) {
  dif_toggle_t state;
  EXPECT_EQ(dif_sram_ctrl_exec_get_enabled(&sram_ctrl_, nullptr), kDifBadArg);
  EXPECT_EQ(dif_sram_ctrl_exec_get_enabled(nullptr, &state), kDifBadArg);
  EXPECT_EQ(dif_sram_ctrl_exec_get_enabled(nullptr, nullptr), kDifBadArg);
}

TEST_F(ExecGetEnabledTest, Enabled) {
  dif_toggle_t state;
  EXPECT_READ32(SRAM_CTRL_EXEC_REG_OFFSET, kMultiBitBool4True);
  EXPECT_EQ(dif_sram_ctrl_exec_get_enabled(&sram_ctrl_, &state), kDifOk);
  EXPECT_EQ(state, kDifToggleEnabled);
}

TEST_F(ExecGetEnabledTest, Disabled) {
  dif_toggle_t state = kDifToggleEnabled;
  EXPECT_READ32(SRAM_CTRL_EXEC_REG_OFFSET, kMultiBitBool4False);
  EXPECT_EQ(dif_sram_ctrl_exec_get_enabled(&sram_ctrl_, &state), kDifOk);
  EXPECT_EQ(state, kDifToggleDisabled);

  state = kDifToggleEnabled;
  EXPECT_READ32(SRAM_CTRL_EXEC_REG_OFFSET, 0);
  EXPECT_EQ(dif_sram_ctrl_exec_get_enabled(&sram_ctrl_, &state), kDifOk);
  EXPECT_EQ(state, kDifToggleDisabled);

  state = kDifToggleEnabled;
  EXPECT_READ32(SRAM_CTRL_EXEC_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_sram_ctrl_exec_get_enabled(&sram_ctrl_, &state), kDifOk);
  EXPECT_EQ(state, kDifToggleDisabled);
}

class ExecSetEnabledTest : public SramCtrlTest {};

TEST_F(ExecSetEnabledTest, NullArgs) {
  EXPECT_EQ(dif_sram_ctrl_exec_set_enabled(nullptr, kDifToggleEnabled),
            kDifBadArg);
  EXPECT_EQ(dif_sram_ctrl_exec_set_enabled(nullptr, kDifToggleDisabled),
            kDifBadArg);
}

TEST_F(ExecSetEnabledTest, Locked) {
  EXPECT_READ32(SRAM_CTRL_EXEC_REGWEN_REG_OFFSET, 0x0);
  EXPECT_EQ(dif_sram_ctrl_exec_set_enabled(&sram_ctrl_, kDifToggleEnabled),
            kDifLocked);

  EXPECT_READ32(SRAM_CTRL_EXEC_REGWEN_REG_OFFSET, 0x0);
  EXPECT_EQ(dif_sram_ctrl_exec_set_enabled(&sram_ctrl_, kDifToggleDisabled),
            kDifLocked);
}

TEST_F(ExecSetEnabledTest, Enabled) {
  EXPECT_READ32(SRAM_CTRL_EXEC_REGWEN_REG_OFFSET, 0x1);
  EXPECT_WRITE32(SRAM_CTRL_EXEC_REG_OFFSET, kMultiBitBool4True);
  EXPECT_EQ(dif_sram_ctrl_exec_set_enabled(&sram_ctrl_, kDifToggleEnabled),
            kDifOk);

  EXPECT_READ32(SRAM_CTRL_EXEC_REGWEN_REG_OFFSET, 0x1);
  EXPECT_WRITE32(SRAM_CTRL_EXEC_REG_OFFSET, kMultiBitBool4False);
  EXPECT_EQ(dif_sram_ctrl_exec_set_enabled(&sram_ctrl_, kDifToggleDisabled),
            kDifOk);
}

class LockTest : public SramCtrlTest {};

TEST_F(LockTest, NullArgs) {
  EXPECT_EQ(dif_sram_ctrl_lock(nullptr, kDifSramCtrlLockCtrl), kDifBadArg);
  EXPECT_EQ(dif_sram_ctrl_lock(nullptr, kDifSramCtrlLockExec), kDifBadArg);
}

TEST_F(LockTest, Error) {
  dif_sram_ctrl_lock_t invalid_enum_variant =
      static_cast<dif_sram_ctrl_lock_t>(std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(dif_sram_ctrl_lock(&sram_ctrl_, invalid_enum_variant), kDifError);
}

TEST_F(LockTest, LockCtrl) {
  EXPECT_WRITE32(SRAM_CTRL_CTRL_REGWEN_REG_OFFSET, 0x0);
  EXPECT_EQ(dif_sram_ctrl_lock(&sram_ctrl_, kDifSramCtrlLockCtrl), kDifOk);
  EXPECT_WRITE32(SRAM_CTRL_CTRL_REGWEN_REG_OFFSET, 0x0);
  EXPECT_EQ(dif_sram_ctrl_lock(&sram_ctrl_, kDifSramCtrlLockCtrl), kDifOk);
}

TEST_F(LockTest, LockExec) {
  EXPECT_WRITE32(SRAM_CTRL_EXEC_REGWEN_REG_OFFSET, 0x0);
  EXPECT_EQ(dif_sram_ctrl_lock(&sram_ctrl_, kDifSramCtrlLockExec), kDifOk);
  EXPECT_WRITE32(SRAM_CTRL_EXEC_REGWEN_REG_OFFSET, 0x0);
  EXPECT_EQ(dif_sram_ctrl_lock(&sram_ctrl_, kDifSramCtrlLockExec), kDifOk);
}

class IsLockedTest : public SramCtrlTest {};

TEST_F(IsLockedTest, NullArgs) {
  bool is_locked;
  EXPECT_EQ(dif_sram_ctrl_is_locked(nullptr, kDifSramCtrlLockCtrl, &is_locked),
            kDifBadArg);
  EXPECT_EQ(dif_sram_ctrl_is_locked(nullptr, kDifSramCtrlLockCtrl, nullptr),
            kDifBadArg);
  EXPECT_EQ(dif_sram_ctrl_is_locked(&sram_ctrl_, kDifSramCtrlLockCtrl, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_sram_ctrl_is_locked(nullptr, kDifSramCtrlLockExec, &is_locked),
            kDifBadArg);
  EXPECT_EQ(dif_sram_ctrl_is_locked(nullptr, kDifSramCtrlLockExec, nullptr),
            kDifBadArg);
  EXPECT_EQ(dif_sram_ctrl_is_locked(&sram_ctrl_, kDifSramCtrlLockExec, nullptr),
            kDifBadArg);
}

TEST_F(IsLockedTest, Error) {
  bool is_locked;
  dif_sram_ctrl_lock_t invalid_enum_variant =
      static_cast<dif_sram_ctrl_lock_t>(std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(
      dif_sram_ctrl_is_locked(&sram_ctrl_, invalid_enum_variant, &is_locked),
      kDifError);
}

TEST_F(IsLockedTest, Ctrl) {
  bool is_locked = true;
  EXPECT_READ32(SRAM_CTRL_CTRL_REGWEN_REG_OFFSET, 0x1);
  EXPECT_EQ(
      dif_sram_ctrl_is_locked(&sram_ctrl_, kDifSramCtrlLockCtrl, &is_locked),
      kDifOk);
  EXPECT_EQ(is_locked, false);

  is_locked = false;
  EXPECT_READ32(SRAM_CTRL_CTRL_REGWEN_REG_OFFSET, 0x0);
  EXPECT_EQ(
      dif_sram_ctrl_is_locked(&sram_ctrl_, kDifSramCtrlLockCtrl, &is_locked),
      kDifOk);
  EXPECT_EQ(is_locked, true);
}

TEST_F(IsLockedTest, Exec) {
  bool is_locked = true;
  EXPECT_READ32(SRAM_CTRL_EXEC_REGWEN_REG_OFFSET, 0x1);
  EXPECT_EQ(
      dif_sram_ctrl_is_locked(&sram_ctrl_, kDifSramCtrlLockExec, &is_locked),
      kDifOk);
  EXPECT_EQ(is_locked, false);

  is_locked = false;
  EXPECT_READ32(SRAM_CTRL_EXEC_REGWEN_REG_OFFSET, 0x0);
  EXPECT_EQ(
      dif_sram_ctrl_is_locked(&sram_ctrl_, kDifSramCtrlLockExec, &is_locked),
      kDifOk);
  EXPECT_EQ(is_locked, true);
}

}  // namespace
}  // namespace dif_sram_ctrl_autogen_unittest
