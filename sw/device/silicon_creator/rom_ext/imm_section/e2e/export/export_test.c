// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Declare the shared symbols
extern const char imm_shared_test_string[];
extern int imm_shared_test_add(int a, int b);
extern void *imm_shared_memcpy(void *dest, const void *src, size_t n);

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  LOG_INFO("Running imm_section export test...");

  // 1. Test test_add
  int sum = imm_shared_test_add(2, 3);
  LOG_INFO("test_add(2, 3) = %d", sum);
  if (sum != 5) {
    LOG_ERROR("Expected test_add(2, 3) to be 5, got %d", sum);
    return false;
  }

  // 2. Test test_string
  LOG_INFO("test_string = '%s'", imm_shared_test_string);
  const char expected_string[] = "Hello from test imm_section!";
  if (memcmp(imm_shared_test_string, expected_string,
             sizeof(expected_string)) != 0) {
    LOG_ERROR("Expected test_string '%s', got '%s'", expected_string,
              imm_shared_test_string);
    return false;
  }

  // 3. Test memcpy
  char src[] = "Shared memcpy works!";
  char dst[32];
  memset(dst, 0, sizeof(dst));

  imm_shared_memcpy(dst, src, sizeof(src));

  if (memcmp(dst, src, sizeof(src)) != 0) {
    LOG_ERROR("Expected memcpy destination '%s', got '%s'", src, dst);
    return false;
  }

  return true;
}
