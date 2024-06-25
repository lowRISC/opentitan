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

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "i2c_regs.h"  // Generated.

static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "This test assumes the target platform is little endian.");

OTTF_DEFINE_TEST_CONFIG();

enum {
  kDeviceAddr = 0x51,
  kDeviceIdAddr = 0xF8 >> 1,

  // Registers values
  kManufacturerId = 0x00A,
  kProductId = 0x510,

  kDefaultTimeoutMicros = 5000,

  kI2cInstances = 3,
};

static status_t write_byte(dif_i2c_t *i2c, const uint8_t addr[2],
                           uint8_t byte) {
  uint8_t data[3] = {addr[0], addr[1], byte};
  return i2c_testutils_write(i2c, kDeviceAddr, sizeof(data), data, false);
}

static status_t read_byte(dif_i2c_t *i2c, const uint8_t addr[2],
                          uint8_t *byte) {
  TRY(i2c_testutils_write(i2c, kDeviceAddr, 2, addr, true));
  return i2c_testutils_read(i2c, kDeviceAddr, 1, byte, kDefaultTimeoutMicros);
}

static status_t read_device_id(dif_i2c_t *i2c) {
  // Reading the manufacturer and product IDs of this device works as follows:
  // 1. Instead of the device address, use the "DeviceID address" word `F8`.
  // 2. Write the device address of the FRAM device (`kDeviceAddr`).
  // 3. Read 3 bytes - the manufacturer and product IDs are 12 bits each.

  uint8_t cmd = kDeviceAddr << 1;
  uint8_t data[3] = {0x00, 0x00, 0x00};

  TRY(i2c_testutils_write(i2c, kDeviceIdAddr, 1, &cmd, true));
  TRY(i2c_testutils_read(i2c, kDeviceIdAddr, sizeof(data), data,
                         kDefaultTimeoutMicros));

  // Extract the 12-bit manufacturer and product IDs from the 24 bits of data.

  uint16_t manuf_id = (uint16_t)((uint16_t)data[0] << 8) + (data[1] >> 4);
  uint16_t product_id = (uint16_t)((uint16_t)(data[1] & 0x0F) << 8) + data[2];

  TRY_CHECK(manuf_id == kManufacturerId, "Unexpected value 0x%x", data);
  TRY_CHECK(product_id == kProductId, "Unexpected value 0x%x", data);

  return OK_STATUS();
}

static status_t write_read_byte(dif_i2c_t *i2c) {
  // Write a byte to some random address.
  const uint8_t kAddr[2] = {0x03, 0x21};
  TRY(write_byte(i2c, kAddr, 0xAB));

  // Read back the data at that address.
  uint8_t read_data = 0x00;
  TRY(read_byte(i2c, kAddr, &read_data));

  TRY_CHECK(read_data == 0xAB, "Unexpected value: 0x%02x", read_data);

  // Overwrite the address that was just written to so that the success state
  // doesn't persist between test runs.
  TRY(write_byte(i2c, kAddr, 0xFF));
  TRY(read_byte(i2c, kAddr, &read_data));
  TRY_CHECK(read_data == 0xFF, "Unexpected value: 0x%02x", read_data);

  return OK_STATUS();
}

static status_t write_read_page(dif_i2c_t *i2c) {
  // Write multiple bytes at once to some address.
  const uint8_t kAddr[2] = {0x02, 0x01};
  uint8_t data[5] = {kAddr[0], kAddr[1], 0xAB, 0xCD, 0xEF};
  TRY(i2c_testutils_write(i2c, kDeviceAddr, sizeof(data), data, false));

  // Read back 2 of the 3 bytes written to that address.
  uint8_t read_data[2] = {0x00, 0x00};
  TRY(i2c_testutils_write(i2c, kDeviceAddr, sizeof(kAddr), kAddr, true));
  TRY(i2c_testutils_read(i2c, kDeviceAddr, sizeof(read_data), read_data,
                         kDefaultTimeoutMicros));

  // Check the read bytes match what we wrote.
  TRY_CHECK_ARRAYS_EQ(read_data, data + 2, sizeof(read_data));

  // The address counter should now be at the third (and final) byte. Read it.
  uint8_t last_byte = 0x00;
  TRY(i2c_testutils_read(i2c, kDeviceAddr, 1, &last_byte,
                         kDefaultTimeoutMicros));

  TRY_CHECK(last_byte == data[4], "Unexpected value: 0x%02x", last_byte);

  // Erase the values we just wrote to prevent the success state persisting
  // between test runs.
  uint8_t erase_data[5] = {kAddr[0], kAddr[1], 0xFF, 0xFF, 0xFF};
  TRY(i2c_testutils_write(i2c, kDeviceAddr, sizeof(erase_data), erase_data,
                          false));
  TRY(i2c_testutils_write(i2c, kDeviceAddr, sizeof(kAddr), kAddr, true));
  uint8_t erase_read[3] = {0x00, 0x00, 0x00};
  TRY(i2c_testutils_read(i2c, kDeviceAddr, sizeof(erase_read), erase_read,
                         kDefaultTimeoutMicros));

  // Check the over-written byte match the new erased value.
  TRY_CHECK_ARRAYS_EQ(erase_read, erase_data + 2, sizeof(erase_read));

  return OK_STATUS();
}

static status_t throughput(dif_i2c_t *i2c, uint32_t expected_kbps) {
  enum { kTimeoutMicros = 1000 * 1000, kTxSize = 512 };

  dif_rv_core_ibex_t rv_core_ibex;
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  const uint8_t kAddr[2] = {0x04, 0x00};
  uint8_t data[kTxSize + sizeof(kAddr)] = {kAddr[0], kAddr[1]};
  // Init buffer with random data.
  for (int i = sizeof(kAddr); i < sizeof(data); ++i) {
    uint32_t rand;
    TRY(rv_core_ibex_testutils_get_rnd_data(&rv_core_ibex, 2000, &rand));
    data[i] = rand & 0xFF;
  }
  ibex_timeout_t timer = ibex_timeout_init(kTimeoutMicros);
  TRY(i2c_testutils_write(i2c, kDeviceAddr, sizeof(data), data, false));
  IBEX_TRY_SPIN_FOR(TRY(i2c_testutils_fmt_fifo_empty(i2c)) == true,
                    kTimeoutMicros);
  uint64_t elapsed = ibex_timeout_elapsed(&timer);
  uint32_t kbps = (kTxSize * 8 * 1000) / (uint32_t)elapsed;
  LOG_INFO("Wrote %u bytes, in %u micros, %u kbps. Expected was %u kbps",
           kTxSize, (uint32_t)elapsed, kbps, expected_kbps);
  TRY_CHECK(kbps >= expected_kbps, "%u kbps is less than %u kpbs", kbps,
            expected_kbps);

  uint8_t read_data[kTxSize] = {0};
  TRY(i2c_testutils_write(i2c, kDeviceAddr, sizeof(kAddr), kAddr, true));
  timer = ibex_timeout_init(kTimeoutMicros);
  TRY(i2c_testutils_read(i2c, kDeviceAddr, kTxSize, read_data, kTimeoutMicros));
  elapsed = ibex_timeout_elapsed(&timer);
  kbps = (kTxSize * 8 * 1000) / (uint32_t)elapsed;
  LOG_INFO("Read %u bytes, in %u micros, %u kbps. Expected was %u kbps",
           kTxSize, (uint32_t)elapsed, kbps, expected_kbps);
  TRY_CHECK(kbps >= expected_kbps);
  // Check the read bytes match what we wrote.
  TRY_CHECK_ARRAYS_EQ(read_data, data + 2, sizeof(read_data));

  return OK_STATUS();
}

static status_t i2c_configure(dif_i2c_t *i2c, dif_pinmux_t *pinmux,
                              uint8_t i2c_instance,
                              i2c_pinmux_platform_id_t platform) {
  const uintptr_t kI2cBaseAddrTable[] = {TOP_EARLGREY_I2C0_BASE_ADDR,
                                         TOP_EARLGREY_I2C1_BASE_ADDR,
                                         TOP_EARLGREY_I2C2_BASE_ADDR};
  TRY_CHECK(i2c_instance < ARRAYSIZE(kI2cBaseAddrTable));

  mmio_region_t base_addr =
      mmio_region_from_addr(kI2cBaseAddrTable[i2c_instance]);
  TRY(dif_i2c_init(base_addr, i2c));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);

  TRY(i2c_testutils_select_pinmux(pinmux, i2c_instance, platform));

  TRY(dif_i2c_host_set_enabled(i2c, kDifToggleEnabled));

  return OK_STATUS();
}

static status_t test_shutdown(dif_i2c_t *i2c, dif_pinmux_t *pinmux,
                              uint8_t i2c_instance) {
  TRY(dif_i2c_host_set_enabled(i2c, kDifToggleDisabled));
  return i2c_testutils_detach_pinmux(pinmux, i2c_instance);
}

typedef struct test_setup {
  dif_i2c_speed_t speed;
  uint32_t kbps;
} test_setup_t;

const test_setup_t kSetup[] = {
    // kbps: We discount 85% for the start and stop bits.
    // We also have to discount a factor to account for rounding errors.
    // The rounding error becomes higher with higher speeds, as the i2c clock
    // approaches the peripheral clock.
    {.speed = kDifI2cSpeedStandard, .kbps = (uint32_t)(100 * 0.984 * 0.85)},
    {.speed = kDifI2cSpeedFast, .kbps = (uint32_t)(400 * 0.92 * 0.85)},
    {.speed = kDifI2cSpeedFastPlus, .kbps = (uint32_t)(1000 * 0.55 * 0.75)}};

bool test_main(void) {
  dif_pinmux_t pinmux;
  dif_i2c_t i2c;

  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  i2c_pinmux_platform_id_t platform = I2cPinmuxPlatformIdCw310Pmod;
  status_t test_result = OK_STATUS();
  for (uint8_t i2c_instance = 0; i2c_instance < kI2cInstances; ++i2c_instance) {
    LOG_INFO("Testing i2c%d", i2c_instance);
    CHECK_STATUS_OK(i2c_configure(&i2c, &pinmux, i2c_instance, platform));

    for (size_t i = 0; i < ARRAYSIZE(kSetup); ++i) {
      CHECK_STATUS_OK(i2c_testutils_set_speed(&i2c, kSetup[i].speed));
      EXECUTE_TEST(test_result, read_device_id, &i2c);
      EXECUTE_TEST(test_result, write_read_byte, &i2c);
      EXECUTE_TEST(test_result, write_read_page, &i2c);
      EXECUTE_TEST(test_result, throughput, &i2c, kSetup[i].kbps);
      CHECK_STATUS_OK(test_result);
    }
    CHECK_STATUS_OK(test_shutdown(&i2c, &pinmux, i2c_instance));
  }
  return status_ok(test_result);
}
