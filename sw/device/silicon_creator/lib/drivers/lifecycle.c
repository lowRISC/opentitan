// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"

#include <assert.h>
#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "lc_ctrl_regs.h"

enum {
  kBase = TOP_EARLGREY_LC_CTRL_BASE_ADDR,
};

lifecycle_state_t lifecycle_state_get(void) {
  uint32_t raw_state = lifecycle_raw_state_get();

  switch (launder32(raw_state)) {
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED0:
      HARDENED_CHECK_EQ(raw_state, LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED0);
      return kLcStateTest;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED1:
      HARDENED_CHECK_EQ(raw_state, LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED1);
      return kLcStateTest;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED2:
      HARDENED_CHECK_EQ(raw_state, LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED2);
      return kLcStateTest;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED3:
      HARDENED_CHECK_EQ(raw_state, LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED3);
      return kLcStateTest;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED4:
      HARDENED_CHECK_EQ(raw_state, LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED4);
      return kLcStateTest;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED5:
      HARDENED_CHECK_EQ(raw_state, LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED5);
      return kLcStateTest;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED6:
      HARDENED_CHECK_EQ(raw_state, LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED6);
      return kLcStateTest;
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED7:
      HARDENED_CHECK_EQ(raw_state, LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED7);
      return kLcStateTest;
    case LC_CTRL_LC_STATE_STATE_VALUE_DEV:
      HARDENED_CHECK_EQ(raw_state, LC_CTRL_LC_STATE_STATE_VALUE_DEV);
      return kLcStateDev;
    case LC_CTRL_LC_STATE_STATE_VALUE_PROD:
      HARDENED_CHECK_EQ(raw_state, LC_CTRL_LC_STATE_STATE_VALUE_PROD);
      return kLcStateProd;
    case LC_CTRL_LC_STATE_STATE_VALUE_PROD_END:
      HARDENED_CHECK_EQ(raw_state, LC_CTRL_LC_STATE_STATE_VALUE_PROD_END);
      return kLcStateProdEnd;
    case LC_CTRL_LC_STATE_STATE_VALUE_RMA:
      HARDENED_CHECK_EQ(raw_state, LC_CTRL_LC_STATE_STATE_VALUE_RMA);
      return kLcStateRma;
    default:
      HARDENED_TRAP();
      OT_UNREACHABLE();
  }
}

uint32_t lifecycle_raw_state_get(void) {
  uint32_t value = bitfield_field32_read(
      sec_mmio_read32(kBase + LC_CTRL_LC_STATE_REG_OFFSET),
      LC_CTRL_LC_STATE_STATE_FIELD);
  return value;
}

void lifecycle_device_id_get(lifecycle_device_id_t *device_id) {
  static_assert(
      kLifecycleDeviceIdNumWords == LC_CTRL_PARAM_NUM_DEVICE_ID_WORDS,
      "length of the device_id array does not match the length in hardware");

  size_t i = 0, r = kLifecycleDeviceIdNumWords - 1;
  for (; launder32(i) < kLifecycleDeviceIdNumWords &&
         launder32(r) < kLifecycleDeviceIdNumWords;
       ++i, --r) {
    device_id->device_id[i] = sec_mmio_read32(
        kBase + LC_CTRL_DEVICE_ID_0_REG_OFFSET + i * sizeof(uint32_t));
  }
  HARDENED_CHECK_EQ(i, kLifecycleDeviceIdNumWords);
  HARDENED_CHECK_EQ((uint32_t)r, UINT32_MAX);
}

void lifecycle_hw_rev_get(lifecycle_hw_rev_t *hw_rev) {
  uint32_t reg0 = sec_mmio_read32(kBase + LC_CTRL_HW_REVISION0_REG_OFFSET);
  uint32_t reg1 = sec_mmio_read32(kBase + LC_CTRL_HW_REVISION1_REG_OFFSET);
  *hw_rev = (lifecycle_hw_rev_t){
      .silicon_creator_id = (uint16_t)bitfield_field32_read(
          reg0, LC_CTRL_HW_REVISION0_SILICON_CREATOR_ID_FIELD),
      .product_id = (uint16_t)bitfield_field32_read(
          reg0, LC_CTRL_HW_REVISION0_PRODUCT_ID_FIELD),
      .revision_id = (uint8_t)bitfield_field32_read(
          reg1, LC_CTRL_HW_REVISION1_REVISION_ID_FIELD),
  };
}
