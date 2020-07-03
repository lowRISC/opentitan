// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/hart.h"

#include <stdbool.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/runtime/ibex.h"

extern void wait_for_interrupt(void);

void usleep(uint32_t usec) {
  uint64_t cycles = kClockFreqHz * usec / 1000000;
  uint64_t start = ibex_mcycle_read();
  while ((ibex_mcycle_read() - start) < cycles) {
  }
}

noreturn void abort(void) {
  if (kDeviceStopAddress != 0) {
    mmio_region_t end_sim_addr = mmio_region_from_addr(kDeviceStopAddress);
    // Write all ones to the address, to signal that it was `abort`. The
    // simulator doesn't do anything with the info, but it's good to
    // differentiate from likely `main` return codes (0, 1).
    mmio_region_write32(end_sim_addr, 0x0, 0xFFFFFFFF);
  }

  while (true) {
    wait_for_interrupt();
  }
}
