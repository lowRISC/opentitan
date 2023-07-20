// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_lc_ctrl.h"

#include <cstring>
#include <limits>
#include <utility>

#include "gtest/gtest.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "lc_ctrl_regs.h"  // Generated.

namespace dif_lc_ctrl_unittest {
namespace {
using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Test;

class LcCtrlTest : public Test, public MmioTest {
 protected:
  dif_lc_ctrl_t lc_ = {.base_addr = dev().region()};
};

class StateTest : public LcCtrlTest {};

TEST_F(StateTest, GetState) {
  std::vector<std::pair<uint32_t, dif_lc_ctrl_state_t>> states = {
      {LC_CTRL_LC_STATE_STATE_VALUE_RAW, kDifLcCtrlStateRaw},
      {LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED0,
       kDifLcCtrlStateTestUnlocked0},
      {LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED0, kDifLcCtrlStateTestLocked0},
      {LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED1,
       kDifLcCtrlStateTestUnlocked1},
      {LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED1, kDifLcCtrlStateTestLocked1},
      {LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED2,
       kDifLcCtrlStateTestUnlocked2},
      {LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED2, kDifLcCtrlStateTestLocked2},
      {LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED3,
       kDifLcCtrlStateTestUnlocked3},
      {LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED3, kDifLcCtrlStateTestLocked3},
      {LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED4,
       kDifLcCtrlStateTestUnlocked4},
      {LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED4, kDifLcCtrlStateTestLocked4},
      {LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED5,
       kDifLcCtrlStateTestUnlocked5},
      {LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED5, kDifLcCtrlStateTestLocked5},
      {LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED6,
       kDifLcCtrlStateTestUnlocked6},
      {LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED6, kDifLcCtrlStateTestLocked6},
      {LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED7,
       kDifLcCtrlStateTestUnlocked7},
      {LC_CTRL_LC_STATE_STATE_VALUE_DEV, kDifLcCtrlStateDev},
      {LC_CTRL_LC_STATE_STATE_VALUE_PROD, kDifLcCtrlStateProd},
      {LC_CTRL_LC_STATE_STATE_VALUE_PROD_END, kDifLcCtrlStateProdEnd},
      {LC_CTRL_LC_STATE_STATE_VALUE_RMA, kDifLcCtrlStateRma},
      {LC_CTRL_LC_STATE_STATE_VALUE_SCRAP, kDifLcCtrlStateScrap},

      {LC_CTRL_LC_STATE_STATE_VALUE_POST_TRANSITION,
       kDifLcCtrlStatePostTransition},
      {LC_CTRL_LC_STATE_STATE_VALUE_ESCALATE, kDifLcCtrlStateEscalate},
      {LC_CTRL_LC_STATE_STATE_VALUE_INVALID, kDifLcCtrlStateInvalid},
  };

  for (auto pair : states) {
    dif_lc_ctrl_state_t state;

    EXPECT_READ32(LC_CTRL_LC_STATE_REG_OFFSET,
                  {{LC_CTRL_LC_STATE_STATE_OFFSET, pair.first}});
    EXPECT_DIF_OK(dif_lc_ctrl_get_state(&lc_, &state));
    EXPECT_EQ(state, pair.second);
  }
}

TEST_F(StateTest, GetAttempts) {
  uint8_t attempts;

  EXPECT_READ32(LC_CTRL_LC_TRANSITION_CNT_REG_OFFSET,
                {{LC_CTRL_LC_TRANSITION_CNT_CNT_OFFSET, 13}});
  EXPECT_DIF_OK(dif_lc_ctrl_get_attempts(&lc_, &attempts));
  EXPECT_EQ(attempts, 13);

  EXPECT_READ32(LC_CTRL_LC_TRANSITION_CNT_REG_OFFSET,
                {{LC_CTRL_LC_TRANSITION_CNT_CNT_OFFSET,
                  LC_CTRL_LC_TRANSITION_CNT_CNT_MASK}});
  EXPECT_EQ(dif_lc_ctrl_get_attempts(&lc_, &attempts), kDifError);
}

TEST_F(StateTest, GetStatus) {
  dif_lc_ctrl_status_t status;

  EXPECT_READ32(LC_CTRL_STATUS_REG_OFFSET,
                {
                    {LC_CTRL_STATUS_INITIALIZED_BIT, true},
                    {LC_CTRL_STATUS_READY_BIT, true},
                });
  EXPECT_DIF_OK(dif_lc_ctrl_get_status(&lc_, &status));
  EXPECT_TRUE(bitfield_bit32_read(status, kDifLcCtrlStatusCodeInitialized));
  EXPECT_TRUE(bitfield_bit32_read(status, kDifLcCtrlStatusCodeReady));

  EXPECT_READ32(LC_CTRL_STATUS_REG_OFFSET,
                {
                    {LC_CTRL_STATUS_TRANSITION_ERROR_BIT, true},
                    {LC_CTRL_STATUS_TOKEN_ERROR_BIT, true},
                    {LC_CTRL_STATUS_OTP_ERROR_BIT, true},
                });
  EXPECT_DIF_OK(dif_lc_ctrl_get_status(&lc_, &status));
  EXPECT_TRUE(
      bitfield_bit32_read(status, kDifLcCtrlStatusCodeInvalidTransition));
  EXPECT_TRUE(bitfield_bit32_read(status, kDifLcCtrlStatusCodeBadToken));
  EXPECT_TRUE(bitfield_bit32_read(status, kDifLcCtrlStatusCodeOtpError));
}

TEST_F(StateTest, GetIdState) {
  std::vector<std::pair<uint32_t, dif_lc_ctrl_id_state_t>> states = {
      {LC_CTRL_LC_ID_STATE_STATE_VALUE_BLANK, kDifLcCtrlIdStateBlank},
      {LC_CTRL_LC_ID_STATE_STATE_VALUE_PERSONALIZED,
       kDifLcCtrlIdStatePersonalized},
      {LC_CTRL_LC_ID_STATE_STATE_VALUE_INVALID, kDifLcCtrlIdStateInvalid},
  };

  for (auto pair : states) {
    dif_lc_ctrl_id_state_t state;

    EXPECT_READ32(LC_CTRL_LC_ID_STATE_REG_OFFSET, pair.first);
    EXPECT_DIF_OK(dif_lc_ctrl_get_id_state(&lc_, &state));
    EXPECT_EQ(state, pair.second);
  }
}

TEST_F(StateTest, NullArgs) {
  dif_lc_ctrl_state_t state;
  EXPECT_DIF_BADARG(dif_lc_ctrl_get_state(nullptr, &state));
  EXPECT_DIF_BADARG(dif_lc_ctrl_get_state(&lc_, nullptr));

  uint8_t attempts;
  EXPECT_DIF_BADARG(dif_lc_ctrl_get_attempts(nullptr, &attempts));
  EXPECT_DIF_BADARG(dif_lc_ctrl_get_attempts(&lc_, nullptr));

  dif_lc_ctrl_status_t status;
  EXPECT_DIF_BADARG(dif_lc_ctrl_get_status(nullptr, &status));
  EXPECT_DIF_BADARG(dif_lc_ctrl_get_status(&lc_, nullptr));

  dif_lc_ctrl_id_state_t id_state;
  EXPECT_DIF_BADARG(dif_lc_ctrl_get_id_state(nullptr, &id_state));
  EXPECT_DIF_BADARG(dif_lc_ctrl_get_id_state(&lc_, nullptr));
}

class MutexTest : public LcCtrlTest {};

TEST_F(MutexTest, Acquire) {
  EXPECT_READ32(LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_REG_OFFSET, true);
  EXPECT_WRITE32(LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET, kMultiBitBool8True);
  EXPECT_READ32(LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET, kMultiBitBool8True);
  EXPECT_DIF_OK(dif_lc_ctrl_mutex_try_acquire(&lc_));

  EXPECT_READ32(LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_REG_OFFSET, true);
  EXPECT_WRITE32(LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET, kMultiBitBool8True);
  EXPECT_READ32(LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET, kMultiBitBool8False);
  EXPECT_EQ(dif_lc_ctrl_mutex_try_acquire(&lc_), kDifUnavailable);
}

TEST_F(MutexTest, Release) {
  EXPECT_READ32(LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET, kMultiBitBool8True);
  EXPECT_WRITE32(LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET, kMultiBitBool8False);
  EXPECT_DIF_OK(dif_lc_ctrl_mutex_release(&lc_));

  EXPECT_READ32(LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET, kMultiBitBool8False);
  EXPECT_EQ(dif_lc_ctrl_mutex_release(&lc_), kDifError);
}

TEST_F(MutexTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_lc_ctrl_mutex_try_acquire(nullptr));
  EXPECT_DIF_BADARG(dif_lc_ctrl_mutex_release(nullptr));
}

TEST_F(MutexTest, LockMutexClaim) {
  EXPECT_WRITE32(LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_REG_OFFSET, false);
  EXPECT_DIF_OK(dif_lc_ctrl_sw_mutex_lock(&lc_));
  EXPECT_READ32(LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_REG_OFFSET, false);
  EXPECT_EQ(dif_lc_ctrl_mutex_try_acquire(&lc_), kDifLocked);
}

class ConfigureTest : public LcCtrlTest {};

TEST_F(ConfigureTest, SuccessNoToken) {
  EXPECT_READ32(LC_CTRL_TRANSITION_REGWEN_REG_OFFSET, true);
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TARGET_REG_OFFSET,
                 LC_CTRL_TRANSITION_TARGET_STATE_VALUE_PROD);
  EXPECT_WRITE32(LC_CTRL_TRANSITION_CTRL_REG_OFFSET, 0x0);
  EXPECT_DIF_OK(
      dif_lc_ctrl_configure(&lc_, kDifLcCtrlStateProd, false, nullptr));
}

TEST_F(ConfigureTest, SucessWithToken) {
  dif_lc_ctrl_token_t token = {"this is a token"};

  EXPECT_READ32(LC_CTRL_TRANSITION_REGWEN_REG_OFFSET, true);
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TARGET_REG_OFFSET,
                 LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED2);
  EXPECT_WRITE32(LC_CTRL_TRANSITION_CTRL_REG_OFFSET, 0x1);
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TOKEN_0_REG_OFFSET, LeInt("this"));
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TOKEN_1_REG_OFFSET, LeInt(" is "));
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TOKEN_2_REG_OFFSET, LeInt("a to"));
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TOKEN_3_REG_OFFSET, LeInt("ken\0"));
  EXPECT_DIF_OK(
      dif_lc_ctrl_configure(&lc_, kDifLcCtrlStateTestUnlocked2, true, &token));

  EXPECT_READ32(LC_CTRL_TRANSITION_REGWEN_REG_OFFSET, true);
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TARGET_REG_OFFSET,
                 LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED6);
  EXPECT_WRITE32(LC_CTRL_TRANSITION_CTRL_REG_OFFSET, 0x1);
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TOKEN_0_REG_OFFSET, LeInt("this"));
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TOKEN_1_REG_OFFSET, LeInt(" is "));
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TOKEN_2_REG_OFFSET, LeInt("a to"));
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TOKEN_3_REG_OFFSET, LeInt("ken\0"));
  EXPECT_DIF_OK(
      dif_lc_ctrl_configure(&lc_, kDifLcCtrlStateTestUnlocked6, true, &token));
}

TEST_F(ConfigureTest, Locked) {
  EXPECT_READ32(LC_CTRL_TRANSITION_REGWEN_REG_OFFSET, false);
  EXPECT_EQ(dif_lc_ctrl_configure(&lc_, kDifLcCtrlStateProd, false, nullptr),
            kDifUnavailable);
}

TEST_F(ConfigureTest, NullHandle) {
  dif_lc_ctrl_token_t token = {"this is a token"};
  EXPECT_DIF_BADARG(
      dif_lc_ctrl_configure(nullptr, kDifLcCtrlStateProd, false, &token));
}

class TransitionTest : public LcCtrlTest {};

TEST_F(TransitionTest, Success) {
  EXPECT_READ32(LC_CTRL_TRANSITION_REGWEN_REG_OFFSET, true);
  EXPECT_WRITE32(LC_CTRL_TRANSITION_CMD_REG_OFFSET, true);
  EXPECT_DIF_OK(dif_lc_ctrl_transition(&lc_));
}

TEST_F(TransitionTest, Locked) {
  EXPECT_READ32(LC_CTRL_TRANSITION_REGWEN_REG_OFFSET, false);
  EXPECT_EQ(dif_lc_ctrl_transition(&lc_), kDifUnavailable);
}

TEST_F(TransitionTest, NullHandle) {
  EXPECT_DIF_BADARG(dif_lc_ctrl_transition(nullptr));
}

class OtpVendorTestRegTest : public LcCtrlTest {};

TEST_F(OtpVendorTestRegTest, Read) {
  uint32_t settings_read = 0;
  EXPECT_READ32(LC_CTRL_TRANSITION_REGWEN_REG_OFFSET, true);
  EXPECT_READ32(LC_CTRL_OTP_VENDOR_TEST_CTRL_REG_OFFSET, 0x5A);
  EXPECT_DIF_OK(dif_lc_ctrl_get_otp_vendor_test_reg(&lc_, &settings_read));
  EXPECT_EQ(settings_read, 0x5A);
}

TEST_F(OtpVendorTestRegTest, Write) {
  EXPECT_READ32(LC_CTRL_TRANSITION_REGWEN_REG_OFFSET, true);
  EXPECT_WRITE32(LC_CTRL_OTP_VENDOR_TEST_CTRL_REG_OFFSET, 0xA5);
  EXPECT_DIF_OK(dif_lc_ctrl_set_otp_vendor_test_reg(&lc_, 0xA5));
}

}  // namespace
}  // namespace dif_lc_ctrl_unittest
