// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_lc_ctrl.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/multibits.h"

#include "lc_ctrl_regs.h"  // Generated.

dif_result_t dif_lc_ctrl_get_state(const dif_lc_ctrl_t *lc,
                                   dif_lc_ctrl_state_t *state) {
  if (lc == NULL || state == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(lc->base_addr, LC_CTRL_LC_STATE_REG_OFFSET);
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
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED3:
      *state = kDifLcCtrlStateTestLocked3;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED4:
      *state = kDifLcCtrlStateTestUnlocked4;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED4:
      *state = kDifLcCtrlStateTestLocked4;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED5:
      *state = kDifLcCtrlStateTestUnlocked5;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED5:
      *state = kDifLcCtrlStateTestLocked5;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED6:
      *state = kDifLcCtrlStateTestUnlocked6;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED6:
      *state = kDifLcCtrlStateTestLocked6;
      break;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED7:
      *state = kDifLcCtrlStateTestUnlocked7;
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
      return kDifError;
  }

  return kDifOk;
}

dif_result_t dif_lc_ctrl_get_attempts(const dif_lc_ctrl_t *lc, uint8_t *count) {
  if (lc == NULL || count == NULL) {
    return kDifBadArg;
  }

  uint32_t reg =
      mmio_region_read32(lc->base_addr, LC_CTRL_LC_TRANSITION_CNT_REG_OFFSET);
  uint8_t value =
      (uint8_t)bitfield_field32_read(reg, LC_CTRL_LC_TRANSITION_CNT_CNT_FIELD);
  if (value == LC_CTRL_LC_TRANSITION_CNT_CNT_MASK) {
    return kDifError;
  }

  *count = value;
  return kDifOk;
}

dif_result_t dif_lc_ctrl_get_status(const dif_lc_ctrl_t *lc,
                                    dif_lc_ctrl_status_t *status) {
  if (lc == NULL || status == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(lc->base_addr, LC_CTRL_STATUS_REG_OFFSET);

  dif_lc_ctrl_status_t status_word = 0;

  if (bitfield_bit32_read(reg, LC_CTRL_STATUS_INITIALIZED_BIT)) {
    status_word = bitfield_bit32_write(status_word,
                                       kDifLcCtrlStatusCodeInitialized, true);
  }

  if (bitfield_bit32_read(reg, LC_CTRL_STATUS_READY_BIT)) {
    status_word =
        bitfield_bit32_write(status_word, kDifLcCtrlStatusCodeReady, true);
  }

  if (bitfield_bit32_read(reg, LC_CTRL_STATUS_EXT_CLOCK_SWITCHED_BIT)) {
    status_word = bitfield_bit32_write(status_word,
                                       kDifLcCtrlStatusExtClockSwitched, true);
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

  if (bitfield_bit32_read(reg, LC_CTRL_STATUS_FLASH_RMA_ERROR_BIT)) {
    status_word = bitfield_bit32_write(status_word,
                                       kDifLcCtrlStatusCodeFlashRmaError, true);
  }

  if (bitfield_bit32_read(reg, LC_CTRL_STATUS_OTP_ERROR_BIT)) {
    status_word =
        bitfield_bit32_write(status_word, kDifLcCtrlStatusCodeOtpError, true);
  }

  if (bitfield_bit32_read(reg, LC_CTRL_STATUS_STATE_ERROR_BIT)) {
    status_word =
        bitfield_bit32_write(status_word, kDifLcCtrlStatusCodeCorrupt, true);
  }

  if (bitfield_bit32_read(reg, LC_CTRL_STATUS_BUS_INTEG_ERROR_BIT)) {
    status_word = bitfield_bit32_write(status_word,
                                       kDifLcCtrlStatusCodeBusIntegError, true);
  }

  if (bitfield_bit32_read(reg, LC_CTRL_STATUS_OTP_PARTITION_ERROR_BIT)) {
    status_word = bitfield_bit32_write(status_word,
                                       kDifLcCtrlStatusCodeOtpPartError, true);
  }

  *status = status_word;
  return kDifOk;
}

dif_result_t dif_lc_ctrl_get_id_state(const dif_lc_ctrl_t *lc,
                                      dif_lc_ctrl_id_state_t *state) {
  if (lc == NULL || state == NULL) {
    return kDifBadArg;
  }

  uint32_t reg =
      mmio_region_read32(lc->base_addr, LC_CTRL_LC_ID_STATE_REG_OFFSET);
  switch (reg) {
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
      return kDifError;
  }

  return kDifOk;
}

dif_result_t dif_lc_ctrl_get_hw_rev(const dif_lc_ctrl_t *lc,
                                    dif_lc_ctrl_hw_rev_t *hw_rev) {
  if (lc == NULL || hw_rev == NULL) {
    return kDifBadArg;
  }

  uint32_t reg =
      mmio_region_read32(lc->base_addr, LC_CTRL_HW_REVISION0_REG_OFFSET);
  hw_rev->silicon_creator_id = (uint16_t)bitfield_field32_read(
      reg, LC_CTRL_HW_REVISION0_SILICON_CREATOR_ID_FIELD);
  hw_rev->product_id = (uint16_t)bitfield_field32_read(
      reg, LC_CTRL_HW_REVISION0_PRODUCT_ID_FIELD);
  hw_rev->revision_id = (uint8_t)bitfield_field32_read(
      reg, LC_CTRL_HW_REVISION1_REVISION_ID_FIELD);
  return kDifOk;
}

dif_result_t dif_lc_ctrl_get_device_id(const dif_lc_ctrl_t *lc,
                                       dif_lc_ctrl_device_id_t *device_id) {
  if (lc == NULL || device_id == NULL) {
    return kDifBadArg;
  }

  mmio_region_memcpy_from_mmio32(lc->base_addr, LC_CTRL_DEVICE_ID_0_REG_OFFSET,
                                 device_id->data,
                                 ARRAYSIZE(device_id->data) * sizeof(uint32_t));
  return kDifOk;
}

dif_result_t dif_lc_ctrl_mutex_try_acquire(const dif_lc_ctrl_t *lc) {
  if (lc == NULL) {
    return kDifBadArg;
  }

  // Check that mutex claim via SW is not locked.
  if (mmio_region_read32(lc->base_addr,
                         LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_REG_OFFSET) == 0) {
    return kDifLocked;
  }

  mmio_region_write32(lc->base_addr, LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET,
                      kMultiBitBool8True);
  uint32_t reg =
      mmio_region_read32(lc->base_addr, LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET);
  // If the register is not `kMultiBitBool8True`, that means we failed to take
  // the mutex for whatever reason.
  if (reg != kMultiBitBool8True) {
    return kDifUnavailable;
  } else {
    return kDifOk;
  }
}

dif_result_t dif_lc_ctrl_mutex_release(const dif_lc_ctrl_t *lc) {
  if (lc == NULL) {
    return kDifBadArg;
  }

  uint32_t reg =
      mmio_region_read32(lc->base_addr, LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET);
  if (reg != kMultiBitBool8True) {
    // We're not holding the mutex, which is a programmer error.
    return kDifError;
  }

  mmio_region_write32(lc->base_addr, LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET,
                      kMultiBitBool8False);
  return kDifOk;
}

dif_result_t dif_lc_ctrl_configure(const dif_lc_ctrl_t *lc,
                                   dif_lc_ctrl_state_t state,
                                   bool use_ext_clock,
                                   const dif_lc_ctrl_token_t *token) {
  if (lc == NULL) {
    return kDifBadArg;
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
    case kDifLcCtrlStateTestLocked3:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED3;
      break;
    case kDifLcCtrlStateTestUnlocked4:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED4;
      break;
    case kDifLcCtrlStateTestLocked4:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED4;
      break;
    case kDifLcCtrlStateTestUnlocked5:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED5;
      break;
    case kDifLcCtrlStateTestLocked5:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED5;
      break;
    case kDifLcCtrlStateTestUnlocked6:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED6;
      break;
    case kDifLcCtrlStateTestLocked6:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED6;
      break;
    case kDifLcCtrlStateTestUnlocked7:
      target = LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED7;
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
      return kDifBadArg;
  }

  // Check if the mutex has been acquired.
  if (!mmio_region_read32(lc->base_addr,
                          LC_CTRL_TRANSITION_REGWEN_REG_OFFSET)) {
    return kDifUnavailable;
  }

  // Set the target for the transition.
  mmio_region_write32(lc->base_addr, LC_CTRL_TRANSITION_TARGET_REG_OFFSET,
                      target);

  // Program the clock selection.
  uint32_t ctrl_reg = 0;
  if (use_ext_clock) {
    ctrl_reg = bitfield_bit32_write(
        ctrl_reg, LC_CTRL_TRANSITION_CTRL_EXT_CLOCK_EN_BIT, true);
  } else {
    // Default to internal clock.
    ctrl_reg = bitfield_bit32_write(
        ctrl_reg, LC_CTRL_TRANSITION_CTRL_EXT_CLOCK_EN_BIT, false);
  }
  mmio_region_write32(lc->base_addr, LC_CTRL_TRANSITION_CTRL_REG_OFFSET,
                      ctrl_reg);

  // Fill in a token, if necessary.
  if (token != NULL) {
    for (int i = 0; i < sizeof(token->data); i += sizeof(uint32_t)) {
      uint32_t word;
      memcpy(&word, &token->data[i], sizeof(uint32_t));
      mmio_region_write32(lc->base_addr,
                          LC_CTRL_TRANSITION_TOKEN_0_REG_OFFSET + i, word);
    }
  }

  return kDifOk;
}

dif_result_t dif_lc_ctrl_transition(const dif_lc_ctrl_t *lc) {
  if (lc == NULL) {
    return kDifBadArg;
  }

  // Check if the mutex has been acquired.
  if (!mmio_region_read32(lc->base_addr,
                          LC_CTRL_TRANSITION_REGWEN_REG_OFFSET)) {
    return kDifUnavailable;
  }

  mmio_region_write32(lc->base_addr, LC_CTRL_TRANSITION_CMD_REG_OFFSET, 1);

  return kDifOk;
}

dif_result_t dif_lc_ctrl_set_otp_vendor_test_reg(const dif_lc_ctrl_t *lc,
                                                 uint32_t settings) {
  if (lc == NULL) {
    return kDifBadArg;
  }

  uint32_t busy =
      mmio_region_read32(lc->base_addr, LC_CTRL_TRANSITION_REGWEN_REG_OFFSET);
  if (busy == 0) {
    return kDifUnavailable;
  }

  mmio_region_write32(lc->base_addr, LC_CTRL_OTP_VENDOR_TEST_CTRL_REG_OFFSET,
                      settings);

  return kDifOk;
}

dif_result_t dif_lc_ctrl_get_otp_vendor_test_reg(const dif_lc_ctrl_t *lc,
                                                 uint32_t *settings) {
  if (lc == NULL || settings == NULL) {
    return kDifBadArg;
  }

  uint32_t busy =
      mmio_region_read32(lc->base_addr, LC_CTRL_TRANSITION_REGWEN_REG_OFFSET);
  if (busy == 0) {
    return kDifUnavailable;
  }

  *settings = mmio_region_read32(lc->base_addr,
                                 LC_CTRL_OTP_VENDOR_TEST_CTRL_REG_OFFSET);

  return kDifOk;
}

dif_result_t dif_lc_ctrl_sw_mutex_lock(const dif_lc_ctrl_t *lc) {
  if (lc == NULL) {
    return kDifBadArg;
  }

  // Clear CLAIM_TRANSITION_IF_REGWEN to lock mutex claim from TL-UL side.
  mmio_region_write32(lc->base_addr,
                      LC_CTRL_CLAIM_TRANSITION_IF_REGWEN_REG_OFFSET, 0);

  return kDifOk;
}
