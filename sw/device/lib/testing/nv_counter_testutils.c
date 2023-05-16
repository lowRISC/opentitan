// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/nv_counter_testutils.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "flash_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  kNonVolatileCounterFlashWords = 256,
};
static_assert(kNonVolatileCounterFlashWords ==
                  kFlashCtrlTestUtilsCounterMaxCount,
              "Word count must be equal to max count.");
static_assert(
    FLASH_CTRL_PARAM_BYTES_PER_WORD == sizeof(uint64_t),
    "Elements of the counter array must be the same size as a flash word");
extern char _non_volatile_counter_flash_words[];

OT_SET_BSS_SECTION(".non_volatile_counter_0",
                   uint64_t nv_counter_0[kNonVolatileCounterFlashWords];)
OT_SET_BSS_SECTION(".non_volatile_counter_1",
                   uint64_t nv_counter_1[kNonVolatileCounterFlashWords];)
OT_SET_BSS_SECTION(".non_volatile_counter_2",
                   uint64_t nv_counter_2[kNonVolatileCounterFlashWords];)
OT_SET_BSS_SECTION(".non_volatile_counter_3",
                   uint64_t nv_counter_3[kNonVolatileCounterFlashWords];)

static uint64_t *const kNvCounters[] = {
    nv_counter_0,
    nv_counter_1,
    nv_counter_2,
    nv_counter_3,
};

status_t flash_ctrl_testutils_counter_get(size_t counter, uint32_t *value) {
  TRY_CHECK(value != NULL);
  TRY_CHECK(counter < ARRAYSIZE(kNvCounters));
  TRY_CHECK((uint32_t)&_non_volatile_counter_flash_words ==
            kNonVolatileCounterFlashWords);

  // Use a reverse loop since `flash_ctrl_testutils_counter_set_at_least()` can
  // introduce gaps.
  size_t i = kNonVolatileCounterFlashWords - 1;
  for (; i < kNonVolatileCounterFlashWords; --i) {
    if (kNvCounters[counter][i] == 0) {
      break;
    }
  }
  *value = i + 1;
  return OK_STATUS();
}

status_t flash_ctrl_testutils_counter_increment(
    dif_flash_ctrl_state_t *flash_state, size_t counter) {
  size_t i;
  TRY(flash_ctrl_testutils_counter_get(counter, &i));
  TRY_CHECK(i < kNonVolatileCounterFlashWords,
            "Non-volatile counter %u is at its maximum", counter);
  TRY(flash_ctrl_testutils_counter_set_at_least(flash_state, counter, i + 1));
  uint32_t value;
  TRY(flash_ctrl_testutils_counter_get(counter, &value));
  TRY_CHECK(value == i + 1, "Counter increment failed");
  return OK_STATUS();
}

status_t flash_ctrl_testutils_counter_set_at_least(
    dif_flash_ctrl_state_t *flash_state, size_t counter, uint32_t val) {
  TRY_CHECK(val <= kNonVolatileCounterFlashWords,
            "Non-volatile counter %u new value %u > max value %u", counter, val,
            kNonVolatileCounterFlashWords);
  if (val == 0) {
    return OK_STATUS();
  }
  uint32_t new_val[FLASH_CTRL_PARAM_BYTES_PER_WORD / sizeof(uint32_t)] = {0, 0};
  return flash_ctrl_testutils_write(flash_state,
                                    (uint32_t)&kNvCounters[counter][val - 1] -
                                        TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR,
                                    0, new_val, kDifFlashCtrlPartitionTypeData,
                                    ARRAYSIZE(new_val));
}

// At the beginning of the simulation (Verilator, VCS,etc.),
// the content of the flash might be all-zeros, and thus,
// the NVM counter's inital value might be 256.
// In that case, flash_ctrl_testutils_counter_set_at_least() will not increment
// This function can be used to initialize a NVM counter to zero by filling
// its flash region with non-zero values.
status_t flash_ctrl_testutils_counter_init_zero(
    dif_flash_ctrl_state_t *flash_state, size_t counter) {
  uint32_t new_val[FLASH_CTRL_PARAM_BYTES_PER_WORD / sizeof(uint32_t)] = {0xaa,
                                                                          0xbb};
  for (int ii = 0; ii < kNonVolatileCounterFlashWords; ii++) {
    TRY(flash_ctrl_testutils_erase_and_write_page(
        flash_state,
        (uint32_t)&kNvCounters[counter][ii] -
            TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR,
        0, new_val, kDifFlashCtrlPartitionTypeData, ARRAYSIZE(new_val)));
  }
  return OK_STATUS();
}
