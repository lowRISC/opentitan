// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"

const char test_string[] = "Hello from test imm_section!";

int bss_var;
int data_var = 42;

int test_add(int a, int b) {
#ifdef USE_BSS
  bss_var++;
#endif
#ifdef USE_DATA
  data_var++;
#endif
  return a + b;
}

// Global pointers used to reference the symbols from the entry point,
// preventing the linker from garbage collecting them.
const void *test_string_ref;
const void *test_add_ref;
const void *memcpy_ref;

void _imm_section_start_boot(void) {
  test_string_ref = test_string;
  test_add_ref = (const void *)test_add;
  memcpy_ref = (const void *)memcpy;
}
