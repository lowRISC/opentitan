// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/nv_counter_testutils.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#if defined(USE_RRAM)
#include "sw/device/lib/dif/dif_rram_ctrl.h"
#include "sw/device/lib/testing/rram_ctrl_testutils.h"
#else
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"

#include "hw/top/flash_ctrl_regs.h"  // Generated.
#endif                               // USE_RRAM

#if defined(USE_RRAM)

enum {
  // One aligned RRAM write granule: {value, valid marker, reserved,
  // reserved}. The shared linker script (ottf_common.ld) still reserves a
  // much larger flash-oriented region per counter (256 8-byte words = 2048
  // bytes); RRAM only needs this single 4-word (16-byte) line and simply
  // uses the first bytes of that reserved space.
  kNvRramCounterWords = 4,
};

static_assert(kNvRramCounterWords * sizeof(uint32_t) <= 2048,
              "RRAM counter storage must fit within the non_volatile_counter "
              "section reserved by ottf_common.ld.");

static const uint32_t kNvCounterValid = 0xABBAABBA;

OT_SET_BSS_SECTION(".non_volatile_counter_0",
                   uint32_t nv_counter_0[kNvRramCounterWords];)
OT_SET_BSS_SECTION(".non_volatile_counter_1",
                   uint32_t nv_counter_1[kNvRramCounterWords];)
OT_SET_BSS_SECTION(".non_volatile_counter_2",
                   uint32_t nv_counter_2[kNvRramCounterWords];)
OT_SET_BSS_SECTION(".non_volatile_counter_3",
                   uint32_t nv_counter_3[kNvRramCounterWords];)

static uint32_t *const kNvCounters[] = {
    nv_counter_0,
    nv_counter_1,
    nv_counter_2,
    nv_counter_3,
};

static status_t nv_counter_rram_init(dif_rram_ctrl_state_t *rram) {
  TRY(dif_rram_ctrl_init_state(
      rram, mmio_region_from_addr(TOP_EARLGREY_RRAM_CTRL_CORE_BASE_ADDR)));
  TRY(rram_ctrl_testutils_default_region_access(rram, /*rd_en=*/true,
                                                /*wr_en=*/true,
                                                /*scramble_en=*/false,
                                                /*ecc_en=*/false));
  return OK_STATUS();
}

status_t nv_counter_testutils_counter_get(size_t counter, uint32_t *value) {
  TRY_CHECK(value != NULL);
  TRY_CHECK(counter < ARRAYSIZE(kNvCounters));

  *value = 0;
  if (kNvCounters[counter][1] == kNvCounterValid) {
    *value = kNvCounters[counter][0];
  }
  return OK_STATUS();
}

status_t nv_counter_testutils_counter_increment(size_t counter) {
  dif_rram_ctrl_state_t rram;
  TRY(nv_counter_rram_init(&rram));

  uint32_t before;
  TRY(nv_counter_testutils_counter_get(counter, &before));
  // RRAM writes must be a multiple of 4 words; leaving the last two words
  // unused is simpler than a read-modify-write.
  uint32_t new_val[kNvRramCounterWords] = {before + 1, kNvCounterValid, 0, 0};
  TRY(rram_ctrl_testutils_write(&rram,
                                (uint32_t)&kNvCounters[counter][0] -
                                    TOP_EARLGREY_RRAM_CTRL_HOST_BASE_ADDR,
                                new_val, kDifRramCtrlPartitionTypeData,
                                kNvRramCounterWords));

  uint32_t value;
  TRY(nv_counter_testutils_counter_get(counter, &value));
  TRY_CHECK(value == before + 1, "Counter increment failed");
  return OK_STATUS();
}

#else  // USE_RRAM

enum {
  kNonVolatileCounterFlashWords = 256,
};
static_assert(kNonVolatileCounterFlashWords ==
                  kFlashCtrlTestUtilsCounterMaxCount,
              "Word count must be equal to max count.");
static_assert(
    FLASH_CTRL_PARAM_BYTES_PER_WORD == sizeof(uint64_t),
    "Elements of the counter array must be the same size as a flash word");
extern char _non_volatile_counter_nvm_words[];

OT_SET_BSS_SECTION(".non_volatile_counter_0",
                   uint64_t nv_counter_0[kNonVolatileCounterFlashWords];)
OT_SET_BSS_SECTION(".non_volatile_counter_1",
                   uint64_t nv_counter_1[kNonVolatileCounterFlashWords];)
OT_SET_BSS_SECTION(".non_volatile_counter_2",
                   uint64_t nv_counter_2[kNonVolatileCounterFlashWords];)
OT_SET_BSS_SECTION(".non_volatile_counter_3",
                   uint64_t nv_counter_3[kNonVolatileCounterFlashWords];)

static status_t nv_counter_flash_init(dif_flash_ctrl_state_t *flash) {
  TRY(dif_flash_ctrl_init_state(
      flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(flash_ctrl_testutils_default_region_access(
      flash, /*rd_en=*/true, /*prog_en=*/true, /*erase_en=*/true,
      /*scramble_en=*/false, /*ecc_en=*/false, /*high_endurance_en=*/false));
  return OK_STATUS();
}

static uint64_t *const kNvCounters[] = {
    nv_counter_0,
    nv_counter_1,
    nv_counter_2,
    nv_counter_3,
};

static status_t nv_counter_testutils_counter_set_at_least(size_t counter,
                                                          uint32_t val) {
  TRY_CHECK(val <= kNonVolatileCounterFlashWords,
            "Non-volatile counter %u new value %u > max value %u", counter, val,
            kNonVolatileCounterFlashWords);
  if (val == 0) {
    return OK_STATUS();
  }
  dif_flash_ctrl_state_t flash;
  TRY(nv_counter_flash_init(&flash));
  uint32_t new_val[FLASH_CTRL_PARAM_BYTES_PER_WORD / sizeof(uint32_t)] = {0, 0};
  return flash_ctrl_testutils_write(&flash,
                                    (uint32_t)&kNvCounters[counter][val - 1] -
                                        TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR,
                                    0, new_val, kDifFlashCtrlPartitionTypeData,
                                    ARRAYSIZE(new_val));
}

status_t nv_counter_testutils_counter_get(size_t counter, uint32_t *value) {
  TRY_CHECK(value != NULL);
  TRY_CHECK(counter < ARRAYSIZE(kNvCounters));
  TRY_CHECK((uint32_t)&_non_volatile_counter_nvm_words ==
            kNonVolatileCounterFlashWords);

  // Use a reverse loop since `nv_counter_testutils_counter_set_at_least()` can
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

status_t nv_counter_testutils_counter_increment(size_t counter) {
  size_t i;
  TRY(nv_counter_testutils_counter_get(counter, &i));
  TRY_CHECK(i < kNonVolatileCounterFlashWords,
            "Non-volatile counter %u is at its maximum", counter);
  TRY(nv_counter_testutils_counter_set_at_least(counter, i + 1));
  uint32_t value;
  TRY(nv_counter_testutils_counter_get(counter, &value));
  TRY_CHECK(value == i + 1, "Counter increment failed");
  return OK_STATUS();
}

#endif  // USE_RRAM
