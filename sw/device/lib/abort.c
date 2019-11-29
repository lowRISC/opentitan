// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/common.h"

_Noreturn void abort(void) {
  while (true) {
    asm volatile("wfi;");
  }
}
