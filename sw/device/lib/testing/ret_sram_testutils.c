// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/ret_sram_testutils.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// All the memory used by these utilities should be placed within the the
// owner portion of retention SRAM, as defined in retention_sram.h.

/**
 * This represents the memory used by these utilities.
 */
typedef struct testing_utilities {
  /**
   * An array of counters.
   */
  uint32_t counters[kRetSramTestutilsNumberOfCounters];

  /**
   * A scratch array.
   */
  uint32_t scratch[kRetSramTestutilsScratchSizeAsInts];
} testing_utilities_t;

enum { kOffsetOfTestutils = offsetof(retention_sram_t, owner) };

static_assert(kOffsetOfTestutils + sizeof(testing_utilities_t) <
                  TOP_EARLGREY_RAM_RET_AON_SIZE_BYTES,
              "Testing utilities spill out of retention SRAM");

static_assert(offsetof(retention_sram_t, owner) <= kOffsetOfTestutils,
              "Testing utilities overlap owner area in retention SRAM");

testing_utilities_t *testing_utilities =
    (testing_utilities_t *)(TOP_EARLGREY_RAM_RET_AON_BASE_ADDR +
                            kOffsetOfTestutils);

status_t ret_sram_testutils_counter_clear(size_t counter) {
  TRY_CHECK(counter < kRetSramTestutilsNumberOfCounters);
  testing_utilities->counters[counter] = 0;
  return OK_STATUS();
}

status_t ret_sram_testutils_counter_get(size_t counter, uint32_t *value) {
  TRY_CHECK(value != NULL);
  TRY_CHECK(counter < kRetSramTestutilsNumberOfCounters);
  *value = testing_utilities->counters[counter];
  return OK_STATUS();
}

status_t ret_sram_testutils_counter_increment(size_t counter) {
  uint32_t value;
  TRY_CHECK(counter < kRetSramTestutilsNumberOfCounters);
  value = testing_utilities->counters[counter];
  TRY_CHECK(value < UINT32_MAX);
  testing_utilities->counters[counter]++;
  return OK_STATUS();
}

status_t ret_sram_testutils_counter_set(size_t counter, uint32_t value) {
  TRY_CHECK(counter < kRetSramTestutilsNumberOfCounters);
  testing_utilities->counters[counter] = value;
  return OK_STATUS();
}

status_t ret_sram_testutils_scratch_read(size_t offset, size_t size,
                                         uint32_t *dest) {
  TRY_CHECK(dest != NULL);
  TRY_CHECK(offset + size <= kRetSramTestutilsScratchSizeAsInts);
  for (size_t i = 0; i < size; ++i) {
    dest[i] = testing_utilities->scratch[offset + i];
  }
  return OK_STATUS();
}

status_t ret_sram_testutils_scratch_write(size_t offset, size_t size,
                                          uint32_t *src) {
  TRY_CHECK(src != NULL);
  TRY_CHECK(offset + size <= kRetSramTestutilsScratchSizeAsInts);
  for (size_t i = 0; i < size; ++i) {
    testing_utilities->scratch[offset + i] = src[i];
  }
  return OK_STATUS();
}
