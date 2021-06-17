// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/silicon_creator/lib/base/abs_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/watchdog.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
void hexdump_words(uint32_t addr, size_t len) {
  for (size_t i = 0; i < len; i += 4, addr += 4) {
    if (i % 16 == 0) {
      base_printf(i ? "\n%08x: " : "%08x: ", addr);
    }
    base_printf("%08x ", abs_mmio_read32(addr));
  }
  base_printf("\n");
}

rom_error_t watchdog_pet_test(void) {
  watchdog_init(10);
  hexdump_words(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR, 0x2c);
  for (size_t i = 0; i < 10; ++i) {
    LOG_INFO("watchdog = %x", watchdog_get());
    usleep(5000);
  }
  watchdog_init(0);
  return kErrorOk;
}

rom_error_t watchdog_bite_test(void) {
  watchdog_init(1);
  usleep(11000);
  LOG_INFO("watchdog = %x", watchdog_get());
  watchdog_init(0);
  return kErrorOk;
}

const test_config_t kTestConfig;

bool test_main(void) {
  rom_error_t result = kErrorOk;
  EXECUTE_TEST(result, watchdog_pet_test);
  EXECUTE_TEST(result, watchdog_bite_test);
  return result == kErrorOk;
}
