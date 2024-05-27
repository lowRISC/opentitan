// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"
#include "sw/device/silicon_creator/rom/boot_policy_ptrs.h"

OTTF_DEFINE_TEST_CONFIG();

#ifdef ARRAY_SIZE
static const unsigned char arr[ARRAY_SIZE] = {1, 2, 3};
#endif

bool test_main(void) {
#ifdef ARRAY_SIZE
  for (size_t i = 0; i < ARRAY_SIZE; i += (ARRAY_SIZE / 4)) {
    LOG_INFO("arr[%d] = %d", i, arr[i]);
  }
#endif

  // Check image of the expected size.
  const manifest_t *manifest = boot_policy_manifest_a_get();
  LOG_INFO("Image Length (bytes) = %d", manifest->length);
  CHECK(manifest->length > CHIP_ROM_EXT_SIZE_MAX);
  CHECK(manifest->length <= CHIP_ROM_EXT_RESIZABLE_SIZE_MAX);
  return true;
}
