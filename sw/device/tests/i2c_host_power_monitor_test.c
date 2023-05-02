// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include <assert.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/i2c_testutils.h"
#include "sw/device/lib/testing/rv_core_ibex_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "i2c_regs.h"  // Generated.

static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "This test assumes the target platform is little endian.");

OTTF_DEFINE_TEST_CONFIG();

enum {
  kDeviceAddr = 0x10,

  // Registers
  kManufacturerIdReg = 0xFE,
  kProductIdReg = 0xFD,
  kAccumConfigReg = 0x25,
  kCtrActReg = 0x21,
  kVSensenAvgReg = 0x13,
  kVPowerNReg = 0x17,
  kOcLimitNReg = 0x30,
  // Registers values
  kManufacturerId = 0x54,
  kProductId = 0x7b,
};
/**
 * Declared volatile because it is referenced in the main program flow as well
 * as the ISR.
 */
static dif_rv_core_ibex_t rv_core_ibex;
static dif_pinmux_t pinmux;
static dif_i2c_t i2c;

static status_t read_manufacture_id(void) {
  uint8_t reg = kManufacturerIdReg, data = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, 1, &data));
  TRY_CHECK(data == kManufacturerId, "Unexpected value %x", data);
  return OK_STATUS();
}

static status_t read_product_id(void) {
  uint8_t reg = kProductId, data = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, 1, &data));
  TRY_CHECK(data == kProductId, "Unexpected value %x", data);
  return OK_STATUS();
}

static status_t test_init(void) {
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR);

  TRY(dif_rv_core_ibex_init(base_addr, &rv_core_ibex));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_I2C0_BASE_ADDR);
  TRY(dif_i2c_init(base_addr, &i2c));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);
  TRY(dif_pinmux_init(base_addr, &pinmux));

  TRY(i2c_testutils_connect_i2c_to_pinmux_pins(&pinmux, 0));

  TRY(dif_i2c_host_set_enabled(&i2c, kDifToggleEnabled));
  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  return OK_STATUS();
}

bool test_main(void) {
  status_t test_result;
  CHECK_STATUS_OK(test_init());

  dif_i2c_speed_t speeds[] = {kDifI2cSpeedStandard, kDifI2cSpeedFast,
                              kDifI2cSpeedFastPlus};

  test_result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(speeds); ++i) {
    CHECK_STATUS_OK(i2c_testutils_set_speed(&i2c, speeds[i]));
    EXECUTE_TEST(test_result, read_manufacture_id);
    EXECUTE_TEST(test_result, read_product_id);
  }

  return status_ok(test_result);
}
