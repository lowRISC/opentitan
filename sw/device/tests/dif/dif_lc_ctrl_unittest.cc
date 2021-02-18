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
#include "sw/device/lib/testing/mock_mmio.h"

#include "lc_ctrl_regs.h"  // Generated.

namespace dif_lc_ctrl_unittest {
namespace {
using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;

class LcTest : public testing::Test, public MmioTest {
 protected:
  dif_lc_ctrl_t lc_ = {.params = {.base_addr = dev().region()}};
};

class InitTest : public LcTest {};

TEST_F(InitTest, Success) {
  EXPECT_EQ(dif_lc_ctrl_init({.base_addr = dev().region()}, &lc_),
            kDifLcCtrlOk);
}

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_lc_ctrl_init({.base_addr = dev().region()}, nullptr),
            kDifLcCtrlBadArg);
}

class StateTest : public LcTest {};

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
    EXPECT_EQ(dif_lc_ctrl_get_state(&lc_, &state), kDifLcCtrlOk);
    EXPECT_EQ(state, pair.second);
  }
}

TEST_F(StateTest, GetAttempts) {
  uint8_t attempts;

  EXPECT_READ32(LC_CTRL_LC_TRANSITION_CNT_REG_OFFSET,
                {{LC_CTRL_LC_TRANSITION_CNT_CNT_OFFSET, 13}});
  EXPECT_EQ(dif_lc_ctrl_get_attempts(&lc_, &attempts), kDifLcCtrlAttemptsOk);
  EXPECT_EQ(attempts, 13);

  EXPECT_READ32(LC_CTRL_LC_TRANSITION_CNT_REG_OFFSET,
                {{LC_CTRL_LC_TRANSITION_CNT_CNT_OFFSET,
                  LC_CTRL_LC_TRANSITION_CNT_CNT_MASK}});
  EXPECT_EQ(dif_lc_ctrl_get_attempts(&lc_, &attempts),
            kDifLcCtrlAttemptsTooMany);
}

TEST_F(StateTest, GetStatus) {
  dif_lc_ctrl_status_t status;

  EXPECT_READ32(LC_CTRL_STATUS_REG_OFFSET, {
                                               {LC_CTRL_STATUS_READY_BIT, true},
                                           });
  EXPECT_EQ(dif_lc_ctrl_get_status(&lc_, &status), kDifLcCtrlOk);
  EXPECT_EQ(status, bitfield_bit32_write(0, kDifLcCtrlStatusCodeReady, true));

  EXPECT_READ32(LC_CTRL_STATUS_REG_OFFSET,
                {
                    {LC_CTRL_STATUS_TRANSITION_ERROR_BIT, true},
                    {LC_CTRL_STATUS_TOKEN_ERROR_BIT, true},
                    {LC_CTRL_STATUS_OTP_ERROR_BIT, true},
                });
  EXPECT_EQ(dif_lc_ctrl_get_status(&lc_, &status), kDifLcCtrlOk);
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

    EXPECT_READ32(LC_CTRL_LC_ID_STATE_REG_OFFSET,
                  {{LC_CTRL_LC_ID_STATE_STATE_OFFSET, pair.first}});
    EXPECT_EQ(dif_lc_ctrl_get_id_state(&lc_, &state), kDifLcCtrlOk);
    EXPECT_EQ(state, pair.second);
  }
}

TEST_F(StateTest, NullArgs) {
  dif_lc_ctrl_state_t state;
  EXPECT_EQ(dif_lc_ctrl_get_state(nullptr, &state), kDifLcCtrlBadArg);
  EXPECT_EQ(dif_lc_ctrl_get_state(&lc_, nullptr), kDifLcCtrlBadArg);

  uint8_t attempts;
  EXPECT_EQ(dif_lc_ctrl_get_attempts(nullptr, &attempts),
            kDifLcCtrlAttemptsBadArg);
  EXPECT_EQ(dif_lc_ctrl_get_attempts(&lc_, nullptr), kDifLcCtrlAttemptsBadArg);

  dif_lc_ctrl_status_t status;
  EXPECT_EQ(dif_lc_ctrl_get_status(nullptr, &status), kDifLcCtrlBadArg);
  EXPECT_EQ(dif_lc_ctrl_get_status(&lc_, nullptr), kDifLcCtrlBadArg);

  dif_lc_ctrl_id_state_t id_state;
  EXPECT_EQ(dif_lc_ctrl_get_id_state(nullptr, &id_state), kDifLcCtrlBadArg);
  EXPECT_EQ(dif_lc_ctrl_get_id_state(&lc_, nullptr), kDifLcCtrlBadArg);
}

class AlertTest : public LcTest {};

TEST_F(AlertTest, Force) {
  EXPECT_WRITE32(LC_CTRL_ALERT_TEST_REG_OFFSET,
                 {{LC_CTRL_ALERT_TEST_FATAL_PROG_ERROR_BIT, true}});
  EXPECT_EQ(dif_lc_ctrl_alert_force(&lc_, kDifLcCtrlAlertOtp), kDifLcCtrlOk);
}

TEST_F(AlertTest, NullArgs) {
  EXPECT_EQ(dif_lc_ctrl_alert_force(nullptr, kDifLcCtrlAlertCorrupt),
            kDifLcCtrlBadArg);
}

class MutexTest : public LcTest {};

TEST_F(MutexTest, Acquire) {
  EXPECT_WRITE32(LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET, true);
  EXPECT_READ32(LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET, true);
  EXPECT_EQ(dif_lc_ctrl_mutex_try_acquire(&lc_), kDifLcCtrlMutexOk);

  EXPECT_WRITE32(LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET, true);
  EXPECT_READ32(LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET, false);
  EXPECT_EQ(dif_lc_ctrl_mutex_try_acquire(&lc_), kDifLcCtrlMutexAlreadyTaken);
}

TEST_F(MutexTest, Release) {
  EXPECT_READ32(LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET, true);
  EXPECT_WRITE32(LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET, false);
  EXPECT_EQ(dif_lc_ctrl_mutex_release(&lc_), kDifLcCtrlMutexOk);

  EXPECT_READ32(LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET, false);
  EXPECT_EQ(dif_lc_ctrl_mutex_release(&lc_), kDifLcCtrlMutexError);
}

TEST_F(MutexTest, NullArgs) {
  EXPECT_EQ(dif_lc_ctrl_mutex_try_acquire(nullptr), kDifLcCtrlMutexBadArg);
  EXPECT_EQ(dif_lc_ctrl_mutex_release(nullptr), kDifLcCtrlMutexBadArg);
}

class TransitionTest : public LcTest {};

TEST_F(TransitionTest, NoToken) {
  EXPECT_READ32(LC_CTRL_TRANSITION_REGWEN_REG_OFFSET, true);
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TARGET_REG_OFFSET,
                 LC_CTRL_TRANSITION_TARGET_STATE_VALUE_PROD);
  EXPECT_WRITE32(LC_CTRL_TRANSITION_CMD_REG_OFFSET, true);
  EXPECT_EQ(dif_lc_ctrl_transition(&lc_, kDifLcCtrlStateProd, nullptr),
            kDifLcCtrlMutexOk);
}

TEST_F(TransitionTest, WithToken) {
  dif_lc_ctrl_token_t token = {"this is a token"};

  EXPECT_READ32(LC_CTRL_TRANSITION_REGWEN_REG_OFFSET, true);
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TARGET_REG_OFFSET,
                 LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED2);
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TOKEN_0_REG_OFFSET, LeInt("this"));
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TOKEN_1_REG_OFFSET, LeInt(" is "));
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TOKEN_2_REG_OFFSET, LeInt("a to"));
  EXPECT_WRITE32(LC_CTRL_TRANSITION_TOKEN_3_REG_OFFSET, LeInt("ken\0"));
  EXPECT_WRITE32(LC_CTRL_TRANSITION_CMD_REG_OFFSET, true);
  EXPECT_EQ(dif_lc_ctrl_transition(&lc_, kDifLcCtrlStateTestUnlocked2, &token),
            kDifLcCtrlMutexOk);
}

TEST_F(TransitionTest, Locked) {
  EXPECT_READ32(LC_CTRL_TRANSITION_REGWEN_REG_OFFSET, false);
  EXPECT_EQ(dif_lc_ctrl_transition(&lc_, kDifLcCtrlStateProd, nullptr),
            kDifLcCtrlMutexAlreadyTaken);
}

TEST_F(TransitionTest, NullArgs) {
  dif_lc_ctrl_token_t token = {"this is a token"};
  EXPECT_EQ(dif_lc_ctrl_transition(nullptr, kDifLcCtrlStateProd, &token),
            kDifLcCtrlMutexBadArg);
}
}  // namespace
}  // namespace dif_lc_ctrl_unittest
