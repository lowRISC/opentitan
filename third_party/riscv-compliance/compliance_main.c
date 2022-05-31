// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// These symbols are provided by the riscv-compliance libraries.
extern uint32_t begin_signature[];
extern uint32_t end_signature[];

// This symbol is provided by the genrule that converts the reference
// output file.
extern const uint32_t kExpectedSignature[];

// This symbol is defined in compliance_main.S
extern void run_rvc_test(void);

const test_config_t kTestConfig;
bool test_main(void) {
  run_rvc_test();

  ptrdiff_t words = end_signature - begin_signature;
  CHECK_ARRAYS_EQ(begin_signature, kExpectedSignature, (size_t)words);

  return true;
}
