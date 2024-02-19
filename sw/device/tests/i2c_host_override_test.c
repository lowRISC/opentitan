// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/i2c_testutils.h"
#include "sw/device/lib/testing/rv_core_ibex_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "i2c_regs.h"  // Generated.

static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "This test assumes the target platform is little endian.");

OTTF_DEFINE_TEST_CONFIG();

enum {
  kDefaultTimeoutMicros = 50000,
};

// Test harness will backdoor write to this variable.
static volatile uint8_t backdoor_start = false;

static dif_rv_core_ibex_t rv_core_ibex;
static dif_pinmux_t pinmux;
static dif_i2c_t i2c;

const static volatile uint8_t kBitbangData = 0x56;

static status_t test_override(void) {
  // Start bit
  TRY(dif_i2c_override_drive_pins(&i2c, /*scl=*/1, /*sda=*/1));
  busy_spin_micros(15);
  TRY(dif_i2c_override_drive_pins(&i2c, /*scl=*/1, /*sda=*/0));
  busy_spin_micros(15);
  TRY(dif_i2c_override_drive_pins(&i2c, /*scl=*/0, /*sda=*/0));

  const uint8_t bits = sizeof(kBitbangData) * 8;
  uint16_t sda = 0;
  uint16_t data = (uint8_t)(kBitbangData << 1);  // Add ack.
  for (int i = 0; i <= bits; ++i) {
    busy_spin_micros(15);
    sda = (data >> (bits - i)) & 0x01;
    TRY(dif_i2c_override_drive_pins(&i2c, /*scl=*/0, sda));
    busy_spin_micros(15);
    TRY(dif_i2c_override_drive_pins(&i2c, /*scl=*/1, sda));
    busy_spin_micros(30);
    if (i < bits) {
      TRY(dif_i2c_override_drive_pins(&i2c, /*scl=*/0, sda));
    }
  }

  // Stop bit
  TRY(dif_i2c_override_drive_pins(&i2c, /*scl=*/1, /*sda=*/0));
  busy_spin_micros(15);
  TRY(dif_i2c_override_drive_pins(&i2c, /*scl=*/1, /*sda=*/1));
  busy_spin_micros(15);

  return OK_STATUS();
}

static status_t test_init(void) {
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR);
  TRY(dif_rv_core_ibex_init(base_addr, &rv_core_ibex));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);
  TRY(dif_pinmux_init(base_addr, &pinmux));

  return OK_STATUS();
}

static status_t i2c_detach_instance(uint8_t i2c_instance) {
  TRY(dif_i2c_host_set_enabled(&i2c, kDifToggleDisabled));
  return i2c_testutils_detach_pinmux(&pinmux, i2c_instance);
}

static status_t i2c_configure_instance(uint8_t i2c_instance) {
  const uintptr_t kI2cBaseAddrTable[] = {TOP_EARLGREY_I2C0_BASE_ADDR,
                                         TOP_EARLGREY_I2C1_BASE_ADDR,
                                         TOP_EARLGREY_I2C2_BASE_ADDR};
  LOG_INFO("%d", i2c_instance);
  TRY_CHECK(i2c_instance < ARRAYSIZE(kI2cBaseAddrTable));

  mmio_region_t base_addr =
      mmio_region_from_addr(kI2cBaseAddrTable[i2c_instance]);
  TRY(dif_i2c_init(base_addr, &i2c));

  TRY(i2c_testutils_select_pinmux(&pinmux, i2c_instance,
                                  I2cPinmuxPlatformIdHyper310));

  TRY(dif_i2c_override_set_enabled(&i2c, kDifToggleEnabled));
  TRY(dif_i2c_host_set_enabled(&i2c, kDifToggleEnabled));
  return OK_STATUS();
}

bool test_main(void) {
  status_t test_result;
  CHECK_STATUS_OK(test_init());

  test_result = OK_STATUS();
  for (uint8_t instance = 0; instance < 3; instance++) {
    CHECK_STATUS_OK(i2c_configure_instance(instance));
    OTTF_WAIT_FOR(backdoor_start, kDefaultTimeoutMicros);
    // Wait 1ms for the host start sampling before we start transmission.
    busy_spin_micros(50000);
    EXECUTE_TEST(test_result, test_override);
    backdoor_start = false;
    CHECK_STATUS_OK(i2c_detach_instance(instance));
  }

  return status_ok(test_result);
}
