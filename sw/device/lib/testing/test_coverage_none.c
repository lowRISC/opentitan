// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_coverage.h"

// This NOP function gets linked in when coverage is disabled. See
// `test_coverage_llvm.c` for its actual definition when coverage is enabled.
void test_coverage_send_buffer(void) {}
