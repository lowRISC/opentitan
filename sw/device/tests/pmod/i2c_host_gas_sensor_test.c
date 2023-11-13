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
  kDeviceAddr = 0x59,

  // Commands
  kSerialNumberCmd = 0x3682,
  kMeasureRawCmd = 0x260F,
  kExecSelfTestCmd = 0x280E,
  kTurnHeaterOffCmd = 0x3615,
  kResetCmd = 0x0006,

  // Response values
  kSelfTestPass = 0xD4,
};

static dif_rv_core_ibex_t rv_core_ibex;
static dif_pinmux_t pinmux;
static dif_i2c_t i2c;

static status_t read_serial_number(void) {
  uint8_t cmd[2] = {kSerialNumberCmd >> 8, kSerialNumberCmd & 0xFF};
  uint8_t data[9] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(cmd), cmd, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, sizeof(data), data, 5000));

  // Serial numbers are unique per device, so just check it's not 00 or FF.
  uint8_t all_ff[9] = {0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF};
  uint8_t all_00[9] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
  LOG_INFO(
      "Serial number: [0x%02x, 0x%02x, 0x%02x, 0x%02x, 0x%02x, 0x%02x, 0x%02x, "
      "0x%02x, 0x%02x]",
      data[0], data[1], data[2], data[3], data[4], data[5], data[6], data[7],
      data[8]);
  TRY_CHECK_ARRAYS_NE(data, all_ff, sizeof(data));
  TRY_CHECK_ARRAYS_NE(data, all_00, sizeof(data));

  return OK_STATUS();
}

static status_t measure_raw(void) {
  // Write the "measure raw" command with the default arguments, i.e without
  // humidity compensation.
  uint8_t cmd[8] = {kMeasureRawCmd >> 8,
                    kMeasureRawCmd & 0xFF,
                    0x80,
                    0x00,
                    0xA2,
                    0x66,
                    0x66,
                    0x93};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(cmd), cmd, true));

  // Read back the raw measurement.
  uint8_t data[3] = {0x00, 0x00, 0x00};
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, sizeof(data), data, 30000));

  // AND and OR all the bytes together to check they're not all 0xFF or 0x00.
  uint8_t all_ff[3] = {0xFF, 0xFF, 0xFF};
  uint8_t all_00[3] = {0x00, 0x00, 0x00};
  LOG_INFO("Measured data: [0x%02x, 0x%02x, 0x%02x]", data[0], data[1],
           data[2]);
  TRY_CHECK_ARRAYS_NE(data, all_ff, sizeof(data));
  TRY_CHECK_ARRAYS_NE(data, all_00, sizeof(data));

  return OK_STATUS();
}

static status_t self_test(void) {
  // Write the "measure raw" command with the default arguments, i.e without
  // humidity compensation.
  uint8_t cmd[8] = {kExecSelfTestCmd >> 8, kExecSelfTestCmd & 0xFF};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(cmd), cmd, true));

  // The device will send back the results of the self test.
  uint8_t data[3] = {0x00, 0x00, 0x00};
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, sizeof(data), data, 320000));

  // Check the first byte for the "pass" pattern (the other two bytes are
  // ignored and a CRC).
  TRY_CHECK(data[0] == kSelfTestPass, "Expected self test to pass");

  return OK_STATUS();
}

static status_t turn_heater_off(void) {
  // Turn off the heater, stopping measurements and returning to idle.
  uint8_t cmd[2] = {kTurnHeaterOffCmd >> 8, kTurnHeaterOffCmd & 0xFF};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(cmd), cmd, false));

  busy_spin_micros(1000);

  return OK_STATUS();
}

static status_t test_init(void) {
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR);

  TRY(dif_rv_core_ibex_init(base_addr, &rv_core_ibex));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_I2C2_BASE_ADDR);
  TRY(dif_i2c_init(base_addr, &i2c));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);
  TRY(dif_pinmux_init(base_addr, &pinmux));

  TRY(i2c_testutils_select_pinmux(&pinmux, 2, I2cPinmuxPlatformIdCw310Pmod));

  TRY(dif_i2c_host_set_enabled(&i2c, kDifToggleEnabled));

  return OK_STATUS();
}

bool test_main(void) {
  status_t test_result;
  CHECK_STATUS_OK(test_init());

  // Power up time.
  busy_spin_micros(1000);

  dif_i2c_speed_t speeds[] = {kDifI2cSpeedStandard, kDifI2cSpeedFast};

  test_result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(speeds); ++i) {
    CHECK_STATUS_OK(i2c_testutils_set_speed(&i2c, speeds[i]));
    EXECUTE_TEST(test_result, read_serial_number);
    EXECUTE_TEST(test_result, measure_raw);
    EXECUTE_TEST(test_result, self_test);
    EXECUTE_TEST(test_result, turn_heater_off);
  }

  return status_ok(test_result);
}
