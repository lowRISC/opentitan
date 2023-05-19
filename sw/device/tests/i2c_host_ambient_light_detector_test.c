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
  kDeviceAddr = 0x29,

  // Registers
  kPartIdReg = 0x86,
  kManufacturerIdReg = 0x87,
  kAlsContrReg = 0x80,
  kAlsMeasRateReg = 0x85,
  kAlsDataCh10Reg = 0x88,
  kAlsDataCh11Reg = 0x89,
  kAlsDataCh00Reg = 0x8A,
  kAlsDataCh01Reg = 0x8B,
  kAlsStatusReg = 0x8C,

  // Registers values
  kPartId = 0xA0,
  kManufacturerId = 0x05,
  kCtrlActive = 0x01,
  kMeasRate = 0x01 << 3 | 0x02,

  // Register masks
  kDataStatus = 1 << 2,
};

static dif_rv_core_ibex_t rv_core_ibex;
static dif_pinmux_t pinmux;
static dif_i2c_t i2c;

static status_t read_part_id(void) {
  uint8_t reg = kPartIdReg, data = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, 1, &data));
  TRY_CHECK(data == kPartId, "Unexpected value %x", data);
  return OK_STATUS();
}

static status_t read_manufacturer_id(void) {
  uint8_t reg = kManufacturerIdReg, data = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, 1, &data));
  TRY_CHECK(data == kManufacturerId, "Unexpected value %x", data);
  return OK_STATUS();
}

static status_t write_read_measure_rate(void) {
  // Set the measurement rate to something non-default.
  uint8_t meas_reg = kAlsMeasRateReg;
  uint8_t rate[2] = {meas_reg, kMeasRate};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(rate), rate, true));
  // Read back to confirm the write.
  uint8_t rate_data = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &meas_reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, 1, &rate_data));
  TRY_CHECK(rate_data == kMeasRate, "Unexpected value %x", rate_data);

  return OK_STATUS();
}

static status_t take_measurement(void) {
  // Enable active measurements.
  uint8_t ctrl_reg = kAlsContrReg;
  uint8_t ctrl[2] = {ctrl_reg, kCtrlActive};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(ctrl), ctrl, true));
  // Read back the ctrl register to confirm active measurement mode was set.
  uint8_t ctrl_data = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &ctrl_reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, 1, &ctrl_data));
  TRY_CHECK(ctrl_data == kCtrlActive, "Unexpected value %x", ctrl_data);

  // Poll until the status register sets the "data status" bit.
  uint8_t status_reg = kAlsStatusReg;
  uint8_t status = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &status_reg, true));
  do {
    TRY(i2c_testutils_read(&i2c, kDeviceAddr, sizeof(status), &status));
  } while ((status & kDataStatus) == 0);

  // Read data in the order it's laid out in memory: 10, 11, 00, 01.
  uint8_t data_start = kAlsDataCh10Reg;
  uint8_t data[4] = {0x00, 0x00, 0x00, 0x00};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &data_start, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, sizeof(data), data));

  // Check data isn't all 0x00 or all 0xFF, which are more likely to be errors
  // than real values.
  uint8_t all_ff[4] = {0xFF, 0xFF, 0xFF, 0xFF};
  uint8_t all_00[4] = {0x00, 0x00, 0x00, 0x00};
  LOG_INFO("Measured data: [0x%02x, 0x%02x, 0x%02x, 0x%02x]", data[0], data[1],
           data[2], data[3]);
  TRY_CHECK_ARRAYS_NE(data, all_ff, sizeof(data));
  TRY_CHECK_ARRAYS_NE(data, all_00, sizeof(data));

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

  dif_i2c_speed_t speeds[] = {kDifI2cSpeedStandard, kDifI2cSpeedFast};

  // Give the device 100ms to start up.
  busy_spin_micros(100000);

  test_result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(speeds); ++i) {
    CHECK_STATUS_OK(i2c_testutils_set_speed(&i2c, speeds[i]));
    EXECUTE_TEST(test_result, read_part_id);
    EXECUTE_TEST(test_result, read_manufacturer_id);
    EXECUTE_TEST(test_result, write_read_measure_rate);
    EXECUTE_TEST(test_result, take_measurement);
  }

  return status_ok(test_result);
}
