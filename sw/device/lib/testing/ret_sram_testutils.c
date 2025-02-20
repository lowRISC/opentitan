// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/ret_sram_testutils.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "dt/dt_sram_ctrl.h"  // Generated
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

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

// TODO: Replace with a DT API call when memory size information is exposed
// via dtgen.
#if defined(OPENTITAN_IS_EARLGREY)
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static_assert(kOffsetOfTestutils + sizeof(testing_utilities_t) <
                  TOP_EARLGREY_RAM_RET_AON_SIZE_BYTES,
              "Testing utilities spill out of retention SRAM");
#elif defined(OPENTITAN_IS_DARJEELING)
#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

static_assert(kOffsetOfTestutils + sizeof(testing_utilities_t) <
                  TOP_DARJEELING_RAM_RET_AON_SIZE_BYTES,
              "Testing utilities spill out of retention SRAM");
#else
#error "ret_sram_testutils does not support this top"
#endif

static_assert(offsetof(retention_sram_t, owner) <= kOffsetOfTestutils,
              "Testing utilities overlap owner area in retention SRAM");

testing_utilities_t *testing_utilities = NULL;

void ret_sram_testutils_init(void) {
  testing_utilities =
      (testing_utilities_t *)(dt_sram_ctrl_reg_block(kDtSramCtrlRetAon,
                                                     kDtSramCtrlRegBlockRam) +
                              kOffsetOfTestutils);
}

status_t ret_sram_testutils_counter_clear(size_t counter) {
  TRY_CHECK(testing_utilities != NULL);
  TRY_CHECK(counter < kRetSramTestutilsNumberOfCounters);
  testing_utilities->counters[counter] = 0;
  return OK_STATUS();
}

status_t ret_sram_testutils_counter_get(size_t counter, uint32_t *value) {
  TRY_CHECK(testing_utilities != NULL);
  TRY_CHECK(value != NULL);
  TRY_CHECK(counter < kRetSramTestutilsNumberOfCounters);
  *value = testing_utilities->counters[counter];
  return OK_STATUS();
}

status_t ret_sram_testutils_counter_increment(size_t counter) {
  uint32_t value;
  TRY_CHECK(testing_utilities != NULL);
  TRY_CHECK(counter < kRetSramTestutilsNumberOfCounters);
  value = testing_utilities->counters[counter];
  TRY_CHECK(value < UINT32_MAX);
  testing_utilities->counters[counter]++;
  return OK_STATUS();
}

status_t ret_sram_testutils_counter_set(size_t counter, uint32_t value) {
  TRY_CHECK(testing_utilities != NULL);
  TRY_CHECK(counter < kRetSramTestutilsNumberOfCounters);
  testing_utilities->counters[counter] = value;
  return OK_STATUS();
}

status_t ret_sram_testutils_scratch_read(size_t offset, size_t size,
                                         uint32_t *dest) {
  TRY_CHECK(testing_utilities != NULL);
  TRY_CHECK(dest != NULL);
  TRY_CHECK(offset + size <= kRetSramTestutilsScratchSizeAsInts);
  for (size_t i = 0; i < size; ++i) {
    dest[i] = testing_utilities->scratch[offset + i];
  }
  return OK_STATUS();
}

status_t ret_sram_testutils_scratch_write(size_t offset, size_t size,
                                          uint32_t *src) {
  TRY_CHECK(testing_utilities != NULL);
  TRY_CHECK(src != NULL);
  TRY_CHECK(offset + size <= kRetSramTestutilsScratchSizeAsInts);
  for (size_t i = 0; i < size; ++i) {
    testing_utilities->scratch[offset + i] = src[i];
  }
  return OK_STATUS();
}

status_t ret_sram_testutils_is_testrom(bool *is_testrom) {
  *is_testrom =
      retention_sram_get()
          ->creator
          .reserved[ARRAYSIZE((retention_sram_t){0}.creator.reserved) - 1] ==
      TEST_ROM_IDENTIFIER;

  return OK_STATUS();
}
