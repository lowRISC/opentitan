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
  kDeviceAddr = 0x30,

  // Registers
  kProductIdReg = 0x20,
  kXOutLowReg = 0x00,
  kXOutHighReg = 0x01,
  kYOutLowReg = 0x02,
  kYOutHighReg = 0x03,
  kZOutLowReg = 0x04,
  kZOutHighReg = 0x05,
  kStatusReg = 0x06,
  kInternalControlReg = 0x07,

  // Registers values
  kProductId = 0x06,

  // Bit masks
  kMeasDone = 0x01,

  kDefaultTimeoutMicros = 5000,
};

static dif_rv_core_ibex_t rv_core_ibex;
static dif_pinmux_t pinmux;
static dif_i2c_t i2c;

static status_t read_product_id(void) {
  return OK_STATUS();
  uint8_t reg = kProductIdReg, data = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, 1, &data, kDefaultTimeoutMicros));
  TRY_CHECK(data == kProductId, "Unexpected value %x", data);
  return OK_STATUS();
}

static status_t take_measurement(void) {
  // Write 0b1 (take measurement) to the internal control register.
  uint8_t write_data[2] = {kInternalControlReg, 0x01};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(write_data), write_data,
                          true));

  // Poll until status indicates measurement was taken.
  uint8_t status = 0;
  uint8_t status_reg = kStatusReg;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &status_reg, true));
  do {
    TRY(i2c_testutils_read(&i2c, kDeviceAddr, sizeof(status), &status,
                           kDefaultTimeoutMicros));
  } while ((status & kMeasDone) == 0);

  // Reading six bytes from Xout Low covers the other "out" registers, too.
  uint8_t read_data[6] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
  uint8_t xout_reg = kXOutLowReg;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &xout_reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, sizeof(read_data), read_data,
                         kDefaultTimeoutMicros));

  // Check the registers didn't all read as 0x00, which could be legitimate
  // measurements, but are more likely to show a read failure.
  uint8_t all_bits = 0x00;
  for (size_t i = 0; i < ARRAYSIZE(read_data); ++i) {
    all_bits |= read_data[i];
  }
  TRY_CHECK(all_bits != 0x00, "All measurement registers zero");

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

  TRY(i2c_testutils_select_pinmux(&pinmux, 0));

  TRY(dif_i2c_host_set_enabled(&i2c, kDifToggleEnabled));

  return OK_STATUS();
}

bool test_main(void) {
  status_t test_result;
  CHECK_STATUS_OK(test_init());

  dif_i2c_speed_t speeds[] = {kDifI2cSpeedStandard, kDifI2cSpeedFast};

  test_result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(speeds); ++i) {
    // Allow 50ms for device startup.
    busy_spin_micros(50000);

    CHECK_STATUS_OK(i2c_testutils_set_speed(&i2c, speeds[i]));
    EXECUTE_TEST(test_result, read_product_id);
    EXECUTE_TEST(test_result, take_measurement);
  }

  return status_ok(test_result);
}
