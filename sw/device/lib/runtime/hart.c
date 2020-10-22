// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/hart.h"

#include <stdbool.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/runtime/ibex.h"

extern void wait_for_interrupt(void);

void usleep(uint32_t usec) {
  uint64_t cycles = kClockFreqCpuHz * usec / 1000000;
  uint64_t start = ibex_mcycle_read();
  while ((ibex_mcycle_read() - start) < cycles) {
  }
}

noreturn void abort(void) {
  while (true) {
    wait_for_interrupt();
  }
}
