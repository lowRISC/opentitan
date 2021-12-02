// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"

#include <assert.h>
#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "lc_ctrl_regs.h"

static const char *const kStateNames[] = {
    // clang-format off
    "RAW",
    "TEST_UNLOCKED0",
    "TEST_LOCKED0",
    "TEST_UNLOCKED1",
    "TEST_LOCKED1",
    "TEST_UNLOCKED2",
    "TEST_LOCKED2",
    "TEST_UNLOCKED3",
    "TEST_LOCKED3",
    "TEST_UNLOCKED4",
    "TEST_LOCKED4",
    "TEST_UNLOCKED5",
    "TEST_LOCKED5",
    "TEST_UNLOCKED6",
    "TEST_LOCKED6",
    "TEST_UNLOCKED7",
    "DEV",
    "PROD",
    "PROD_END",
    "RMA",
    "SCRAP",
    "POST_TRANSITION",
    "ESCALATE",
    "INVALID",
    // clang-format on
};

static_assert(ARRAYSIZE(kStateNames) == kLcStateNumStates,
              "length of the kStateNames array doesn't match the "
              "number of states.");

#define LC_ASSERT(a, b) static_assert(a == b, "Bad value for " #a)
LC_ASSERT(kLcStateRaw, LC_CTRL_LC_STATE_STATE_VALUE_RAW);
LC_ASSERT(kLcStateTestUnlocked0, LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED0);
LC_ASSERT(kLcStateTestLocked0, LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED0);
LC_ASSERT(kLcStateTestUnlocked1, LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED1);
LC_ASSERT(kLcStateTestLocked1, LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED1);
LC_ASSERT(kLcStateTestUnlocked2, LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED2);
LC_ASSERT(kLcStateTestLocked2, LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED2);
LC_ASSERT(kLcStateTestUnlocked3, LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED3);
LC_ASSERT(kLcStateTestLocked3, LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED3);
LC_ASSERT(kLcStateTestUnlocked4, LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED4);
LC_ASSERT(kLcStateTestLocked4, LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED4);
LC_ASSERT(kLcStateTestUnlocked5, LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED5);
LC_ASSERT(kLcStateTestLocked5, LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED5);
LC_ASSERT(kLcStateTestUnlocked6, LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED6);
LC_ASSERT(kLcStateTestLocked6, LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED6);
LC_ASSERT(kLcStateTestUnlocked7, LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED7);
LC_ASSERT(kLcStateDev, LC_CTRL_LC_STATE_STATE_VALUE_DEV);
LC_ASSERT(kLcStateProd, LC_CTRL_LC_STATE_STATE_VALUE_PROD);
LC_ASSERT(kLcStateProdEnd, LC_CTRL_LC_STATE_STATE_VALUE_PROD_END);
LC_ASSERT(kLcStateRma, LC_CTRL_LC_STATE_STATE_VALUE_RMA);
LC_ASSERT(kLcStateScrap, LC_CTRL_LC_STATE_STATE_VALUE_SCRAP);
LC_ASSERT(kLcStatePostTransition, LC_CTRL_LC_STATE_STATE_VALUE_POST_TRANSITION);
LC_ASSERT(kLcStateEscalate, LC_CTRL_LC_STATE_STATE_VALUE_ESCALATE);
LC_ASSERT(kLcStateInvalid, LC_CTRL_LC_STATE_STATE_VALUE_INVALID);

enum {
  kBase = TOP_EARLGREY_LC_CTRL_BASE_ADDR,
};

lifecycle_state_t lifecycle_state_get(void) {
  uint32_t value = bitfield_field32_read(
      sec_mmio_read32(kBase + LC_CTRL_LC_STATE_REG_OFFSET),
      LC_CTRL_LC_STATE_STATE_FIELD);
  return (lifecycle_state_t)value;
}

const char *lifecycle_state_name_get(lifecycle_state_t lc_state) {
  // Life cycle state value (`lc_state`) is a 32-bit value that repeats the
  // 5-bit life cycle state index 6 times.
  enum { kStateIndexMask = 0x1f };
  size_t state_index = (uint32_t)lc_state & kStateIndexMask;
  if (state_index >= kLcStateNumStates) {
    state_index = kLcStateInvalid & kStateIndexMask;
  }
  return kStateNames[state_index];
}

void lifecycle_device_id_get(lifecycle_device_id_t *device_id) {
  static_assert(
      kLifecycleDeviceIdNumWords == LC_CTRL_PARAM_NUM_DEVICE_ID_WORDS,
      "length of the device_id array does not match the length in hardware");

  for (size_t i = 0; i < kLifecycleDeviceIdNumWords; ++i) {
    device_id->device_id[i] = sec_mmio_read32(
        kBase + LC_CTRL_DEVICE_ID_0_REG_OFFSET + i * sizeof(uint32_t));
  }
}
