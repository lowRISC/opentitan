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
  kDeviceAddr = 0x1D,

  // Registers
  kDeviceIdReg = 0x00,
  kThreshTapReg = 0x1D,
  kPowerCtrlReg = 0x2D,
  kDataX0Reg = 0x32,
  kDataX1Reg = 0x33,
  kDataY0Reg = 0x34,
  kDataY1Reg = 0x35,
  kDataZ0Reg = 0x36,
  kDataZ1Reg = 0x37,

  // Registers values
  kDeviceId = 0xE5,
  kMeasure = 0x08,
};

static dif_rv_core_ibex_t rv_core_ibex;
static dif_pinmux_t pinmux;
static dif_i2c_t i2c;

static status_t read_device_id(void) {
  uint8_t reg = kDeviceIdReg, data = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, 1, &data));
  TRY_CHECK(data == kDeviceId, "Unexpected value %x", data);
  return OK_STATUS();
}

static status_t read_write_thresh_tap(void) {
  uint8_t reg = kThreshTapReg;

  // Write some value to the THRESH_TAP register.
  uint8_t write_data[2] = {reg, 0xAB};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(write_data), write_data,
                          false));

  // Read the value back to confirm the write.
  uint8_t read_data = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, 1, &read_data));
  TRY_CHECK(read_data == 0xAB, "Unexpected value %x", read_data);

  return OK_STATUS();
}

static status_t take_measurement(void) {
  // Set the power mode to enable measurements.
  uint8_t write_data[2] = {kPowerCtrlReg, kMeasure};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(write_data), write_data,
                          false));

  // Read all six data measurements starting from DATAX0.
  uint8_t data_x_reg = kDataX0Reg;
  uint8_t read_data[6] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &data_x_reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, sizeof(read_data), read_data));

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

  TRY(i2c_testutils_connect_i2c_to_pinmux_pins(&pinmux, 0));

  TRY(dif_i2c_host_set_enabled(&i2c, kDifToggleEnabled));

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
    EXECUTE_TEST(test_result, read_device_id);
    EXECUTE_TEST(test_result, read_write_thresh_tap);
    EXECUTE_TEST(test_result, take_measurement);
  }

  return status_ok(test_result);
}
