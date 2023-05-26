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

  // Other
  kDefaultTimeoutMicros = 5000,
};

static dif_rv_core_ibex_t rv_core_ibex;
static dif_pinmux_t pinmux;
static dif_i2c_t i2c;

static status_t read_manufacture_id(void) {
  uint8_t reg = kManufacturerIdReg, data = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, 1, &data, kDefaultTimeoutMicros));
  TRY_CHECK(data == kManufacturerId, "Unexpected value %x", data);
  return OK_STATUS();
}

static status_t read_product_id(void) {
  uint8_t reg = kProductIdReg, data = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, 1, &data, kDefaultTimeoutMicros));
  TRY_CHECK(data == kProductId, "Unexpected value %x", data);
  return OK_STATUS();
}

static status_t read_write_1byte(void) {
  uint8_t reg = kAccumConfigReg, read_data = 0;

  // Write config=1.
  uint8_t write_data[2] = {reg, 0x01};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(write_data), write_data,
                          true));

  // Check the write worked.
  read_data = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(reg), &reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, sizeof(read_data), &read_data,
                         kDefaultTimeoutMicros));
  TRY_CHECK(read_data == 0x01, "Unexpected value %x", read_data,
            kDefaultTimeoutMicros);

  // Write config=0.
  write_data[1] = 0x00;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(write_data), write_data,
                          true));

  // Check the write worked.
  read_data = 0x01;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(reg), &reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, sizeof(read_data), &read_data,
                         kDefaultTimeoutMicros));
  TRY_CHECK(read_data == 0x00, "Unexpected value %x", read_data);

  return OK_STATUS();
}

static status_t read_write_2bytes(void) {
  uint8_t reg = kOcLimitNReg, read_data[2] = {0};

  // Write new value.
  uint8_t write_data[3] = {reg, 0xCA, 0xFE};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(write_data), write_data,
                          true));

  // Check the new value.
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(reg), &reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, sizeof(read_data), read_data,
                         kDefaultTimeoutMicros));
  TRY_CHECK(read_data[1] == 0xFE && read_data[0] == 0xCA,
            "Unexpected value %02x%02x", read_data[1], read_data[0]);

  return OK_STATUS();
}

static status_t read_write_block(void) {
  uint8_t reg = kOcLimitNReg, read_data[8] = {0};
  uint8_t rnd_data[sizeof(read_data)];
  uint8_t write_data[sizeof(read_data) + 1];

  // Init buffer with random data.
  for (int i = 0; i < sizeof(rnd_data); ++i) {
    uint32_t rand;
    TRY(rv_core_ibex_testutils_get_rnd_data(&rv_core_ibex, 1000, &rand));
    rnd_data[i] = rand & 0xFF;
  }
  write_data[0] = reg;
  memcpy(&write_data[1], rnd_data, sizeof(rnd_data));
  // Write new value.
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(write_data), write_data,
                          true));

  // Check the new value.
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(reg), &reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, sizeof(read_data), read_data,
                         kDefaultTimeoutMicros));
  TRY_CHECK_ARRAYS_EQ(read_data, rnd_data, sizeof(read_data));

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
    EXECUTE_TEST(test_result, read_write_1byte);
    EXECUTE_TEST(test_result, read_write_2bytes);
    EXECUTE_TEST(test_result, read_write_block);
  }

  return status_ok(test_result);
}
