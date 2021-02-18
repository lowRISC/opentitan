// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_lc_ctrl.h"

#include "sw/device/lib/base/memory.h"
#include "lc_ctrl_regs.h"  // Generated.

dif_lc_ctrl_result_t dif_lc_ctrl_init(dif_lc_ctrl_params_t params,
                                      dif_lc_ctrl_t *lc) {
  if (lc == NULL) {
    return kDifLcCtrlBadArg;
  }

  lc->params = params;
  return kDifLcCtrlOk;
}

dif_lc_ctrl_result_t dif_lc_ctrl_get_state(const dif_lc_ctrl_t *lc,
                                           dif_lc_ctrl_state_t *state) {
  if (lc == NULL || state == NULL) {
    return kDifLcCtrlBadArg;
  }

  uint32_t reg =
      mmio_region_read32(lc->params.base_addr, LC_CTRL_LC_STATE_REG_OFFSET);
  switch (bitfield_field32_read(reg, LC_CTRL_LC_STATE_STATE_FIELD)) {
    case LC_CTRL_LC_STATE_STATE_VALUE_RAW:
      *state = kDifLcCtrlStateRaw;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED0:
      *state = kDifLcCtrlStateTestUnlocked0;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED0:
      *state = kDifLcCtrlStateTestLocked0;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED1:
      *state = kDifLcCtrlStateTestUnlocked1;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED1:
      *state = kDifLcCtrlStateTestLocked1;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED2:
      *state = kDifLcCtrlStateTestUnlocked2;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED2:
      *state = kDifLcCtrlStateTestLocked2;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED3:
      *state = kDifLcCtrlStateTestUnlocked3;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_DEV:
      *state = kDifLcCtrlStateDev;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_PROD:
      *state = kDifLcCtrlStateProd;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_PROD_END:
      *state = kDifLcCtrlStateProdEnd;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_RMA:
      *state = kDifLcCtrlStateRma;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_SCRAP:
      *state = kDifLcCtrlStateScrap;
      break;

    case LC_CTRL_LC_STATE_STATE_VALUE_POST_TRANSITION:
      *state = kDifLcCtrlStatePostTransition;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_ESCALATE:
      *state = kDifLcCtrlStateEscalate;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_INVALID:
      *state = kDifLcCtrlStateInvalid;
      break;

    default:
      return kDifLcCtrlError;
  }

  return kDifLcCtrlOk;
}

dif_lc_ctrl_attempts_result_t dif_lc_ctrl_get_attempts(const dif_lc_ctrl_t *lc,
                                                       uint8_t *count) {
  if (lc == NULL || count == NULL) {
    return kDifLcCtrlAttemptsBadArg;
  }

  uint32_t reg = mmio_region_read32(lc->params.base_addr,
                                    LC_CTRL_LC_TRANSITION_CNT_REG_OFFSET);
  uint8_t value =
      bitfield_field32_read(reg, LC_CTRL_LC_TRANSITION_CNT_CNT_FIELD);
  if (value == LC_CTRL_LC_TRANSITION_CNT_CNT_MASK) {
    return kDifLcCtrlAttemptsTooMany;
  }

  *count = value;
  return kDifLcCtrlAttemptsOk;
}

dif_lc_ctrl_result_t dif_lc_ctrl_get_status(const dif_lc_ctrl_t *lc,
                                            dif_lc_ctrl_status_t *status) {
  if (lc == NULL || status == NULL) {
    return kDifLcCtrlBadArg;
  }

  uint32_t reg =
      mmio_region_read32(lc->params.base_addr, LC_CTRL_STATUS_REG_OFFSET);

  dif_lc_ctrl_status_t status_word = 0;

  if (bitfield_bit32_read(reg, LC_CTRL_STATUS_READY_BIT)) {
    status_word =
        bitfield_bit32_write(status_word, kDifLcCtrlStatusCodeReady, true);
  }

  if (bitfield_bit32_read(reg, LC_CTRL_STATUS_TRANSITION_SUCCESSFUL_BIT)) {
    status_word =
        bitfield_bit32_write(status_word, kDifLcCtrlStatusCodeSuccess, true);
  }

  if (bitfield_bit32_read(reg, LC_CTRL_STATUS_TRANSITION_COUNT_ERROR_BIT)) {
    status_word = bitfield_bit32_write(
        status_word, kDifLcCtrlStatusCodeTooManyTransitions, true);
  }

  if (bitfield_bit32_read(reg, LC_CTRL_STATUS_TRANSITION_ERROR_BIT)) {
    status_word = bitfield_bit32_write(
        status_word, kDifLcCtrlStatusCodeInvalidTransition, true);
  }

  if (bitfield_bit32_read(reg, LC_CTRL_STATUS_TOKEN_ERROR_BIT)) {
    status_word =
        bitfield_bit32_write(status_word, kDifLcCtrlStatusCodeBadToken, true);
  }

  if (bitfield_bit32_read(reg, LC_CTRL_STATUS_OTP_ERROR_BIT)) {
    status_word =
        bitfield_bit32_write(status_word, kDifLcCtrlStatusCodeOtpError, true);
  }

  if (bitfield_bit32_read(reg, LC_CTRL_STATUS_STATE_ERROR_BIT)) {
    status_word =
        bitfield_bit32_write(status_word, kDifLcCtrlStatusCodeCorrupt, true);
  }

  *status = status_word;
  return kDifLcCtrlOk;
}

dif_lc_ctrl_result_t dif_lc_ctrl_get_id_state(const dif_lc_ctrl_t *lc,
                                              dif_lc_ctrl_id_state_t *state) {
  if (lc == NULL || state == NULL) {
    return kDifLcCtrlBadArg;
  }

  uint32_t reg =
      mmio_region_read32(lc->params.base_addr, LC_CTRL_LC_ID_STATE_REG_OFFSET);
  switch (bitfield_field32_read(reg, LC_CTRL_LC_ID_STATE_STATE_FIELD)) {
    case LC_CTRL_LC_ID_STATE_STATE_VALUE_BLANK:
      *state = kDifLcCtrlIdStateBlank;
      break;
    case LC_CTRL_LC_ID_STATE_STATE_VALUE_PERSONALIZED:
      *state = kDifLcCtrlIdStatePersonalized;
      break;
    case LC_CTRL_LC_ID_STATE_STATE_VALUE_INVALID:
      *state = kDifLcCtrlIdStateInvalid;
      break;
    default:
      return kDifLcCtrlError;
  }

  return kDifLcCtrlOk;
}

dif_lc_ctrl_result_t dif_lc_ctrl_alert_force(const dif_lc_ctrl_t *lc,
                                             dif_lc_ctrl_alert_t alert) {
  if (lc == NULL) {
    return kDifLcCtrlBadArg;
  }

  bitfield_bit32_index_t alert_idx;
  switch (alert) {
    case kDifLcCtrlAlertOtp:
      alert_idx = LC_CTRL_ALERT_TEST_FATAL_PROG_ERROR_BIT;
      break;
    case kDifLcCtrlAlertCorrupt:
      alert_idx = LC_CTRL_ALERT_TEST_FATAL_STATE_ERROR_BIT;
      break;
    default:
      return kDifLcCtrlBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, alert_idx, true);
  mmio_region_write32(lc->params.base_addr, LC_CTRL_ALERT_TEST_REG_OFFSET, reg);

  return kDifLcCtrlOk;
}

dif_lc_ctrl_mutex_result_t dif_lc_ctrl_mutex_try_acquire(
    const dif_lc_ctrl_t *lc) {
  if (lc == NULL) {
    return kDifLcCtrlMutexBadArg;
  }

  mmio_region_write32(lc->params.base_addr,
                      LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET, 1);
  uint32_t reg = mmio_region_read32(lc->params.base_addr,
                                    LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET);
  // If the register is zero, that means we failed to take the mutex for
  // whatever reason.
  if (reg == 0) {
    return kDifLcCtrlMutexAlreadyTaken;
  } else {
    return kDifLcCtrlMutexOk;
  }
}

dif_lc_ctrl_mutex_result_t dif_lc_ctrl_mutex_release(const dif_lc_ctrl_t *lc) {
  if (lc == NULL) {
    return kDifLcCtrlMutexBadArg;
  }

  uint32_t reg = mmio_region_read32(lc->params.base_addr,
                                    LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET);
  if (reg == 0) {
    // We're not holding the mutex, which is a programmer error.
    return kDifLcCtrlMutexError;
  }

  mmio_region_write32(lc->params.base_addr,
                      LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET, 0);
  return kDifLcCtrlMutexOk;
}

dif_lc_ctrl_mutex_result_t dif_lc_ctrl_transition(
    const dif_lc_ctrl_t *lc, dif_lc_ctrl_state_t state,
    const dif_lc_ctrl_token_t *token) {
  if (lc == NULL) {
    return kDifLcCtrlMutexBadArg;
  }

  uint32_t target;
  switch (state) {
    case kDifLcCtrlStateRaw:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_RAW;
      break;
    case kDifLcCtrlStateTestUnlocked0:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED0;
      break;
    case kDifLcCtrlStateTestLocked0:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED0;
      break;
    case kDifLcCtrlStateTestUnlocked1:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED1;
      break;
    case kDifLcCtrlStateTestLocked1:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED1;
      break;
    case kDifLcCtrlStateTestUnlocked2:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED2;
      break;
    case kDifLcCtrlStateTestLocked2:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED2;
      break;
    case kDifLcCtrlStateTestUnlocked3:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED3;
      break;
    case kDifLcCtrlStateDev:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_DEV;
      break;
    case kDifLcCtrlStateProd:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_PROD;
      break;
    case kDifLcCtrlStateProdEnd:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_PROD_END;
      break;
    case kDifLcCtrlStateRma:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_RMA;
      break;
    case kDifLcCtrlStateScrap:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_SCRAP;
      break;

    default:
      return kDifLcCtrlMutexBadArg;
  }

  uint32_t busy = mmio_region_read32(lc->params.base_addr,
                                     LC_CTRL_TRANSITION_REGWEN_REG_OFFSET);
  if (busy == 0) {
    return kDifLcCtrlMutexAlreadyTaken;
  }

  // Set the target for the transition.
  mmio_region_write32(lc->params.base_addr,
                      LC_CTRL_TRANSITION_TARGET_REG_OFFSET, target);

  // Fill in a token, if necessary.
  if (token != NULL) {
    for (int i = 0; i < sizeof(token->data); i += sizeof(uint32_t)) {
      uint32_t word;
      memcpy(&word, &token->data[i], sizeof(uint32_t));
      mmio_region_write32(lc->params.base_addr,
                          LC_CTRL_TRANSITION_TOKEN_0_REG_OFFSET + i, word);
    }
  }

  // With both parameters set up, schedule the transition.
  mmio_region_write32(lc->params.base_addr, LC_CTRL_TRANSITION_CMD_REG_OFFSET,
                      1);
  return kDifLcCtrlMutexOk;
}
