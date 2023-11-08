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
  kDeviceAddr = 0x52,
  // Default timeout for i2c reads.
  kDefaultTimeoutMicros = 5000,
  // "Acknowledgement polling" timeout - used for waiting until EEPROM has
  // finished writing.
  kAckPollTimeoutMicros = 80000,
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

/**
 * Poll the EEPROM device until it is no longer busy writing.
 *
 * This function performs a zero-byte read with a `kAckPollTimeoutMicros`
 * microsecond timeout. The EEPROM device will not acknowledge the device
 * address until it is finished writing.
 */
static status_t poll_while_busy(dif_i2c_t *i2c) {
  return i2c_testutils_read(i2c, kDeviceAddr, 0, NULL, kAckPollTimeoutMicros);
}

/**
 * Check if an given irq has fired and is pending.
 */
static status_t check_irq(dif_i2c_t *i2c, dif_i2c_irq_t irq) {
  bool irq_fired = false;
  TRY(dif_i2c_irq_is_pending(i2c, irq, &irq_fired));
  TRY_CHECK(irq_fired, "Irq %u not fired", irq);
  TRY(dif_i2c_irq_acknowledge(i2c, irq));
  return OK_STATUS();
}

static status_t write_read_random(dif_i2c_t *i2c) {
  int32_t naks = 0;
  // Write a byte to some random address.
  const uint8_t kAddr[2] = {0x03, 0x21};
  TRY(write_byte(i2c, kAddr, 0xAB));

  // Wait for the write to finish.
  naks = TRY(poll_while_busy(i2c));
  TRY_CHECK(naks > 0, "We should have received naks");

  // Read back the data at that address.
  uint8_t read_data = 0x00;
  TRY(read_byte(i2c, kAddr, &read_data));

  // Check the written byte matches what we wrote.
  TRY_CHECK(read_data == 0xAB, "Unexpected value: 0x%02x", read_data);

  // Erase the value we just wrote to prevent the success state persisting to
  // subsequent runs of the test.
  TRY(write_byte(i2c, kAddr, 0xFF));
  naks = TRY(poll_while_busy(i2c));
  TRY_CHECK(naks > 0, "We should have received naks");
  TRY(read_byte(i2c, kAddr, &read_data));

  // Check the over-written byte matches the new value.
  TRY_CHECK(read_data == 0xFF, "Unexpected value: 0x%02x", read_data);

  return OK_STATUS();
}

static status_t write_read_page(dif_i2c_t *i2c) {
  // Write multiple bytes to the 9th page (of 64 bytes each).
  const uint8_t kAddr[2] = {0x02, 0x01};
  uint8_t data[10] = {kAddr[0], kAddr[1], 0x01, 0x23, 0x45,
                      0x67,     0x89,     0xAB, 0xCD, 0xEF};
  TRY(i2c_testutils_write(i2c, kDeviceAddr, sizeof(data), data, false));

  // Wait for the write to finish.
  TRY(poll_while_busy(i2c));

  // Read back the data at that address.
  uint8_t read_data[8] = {
      0x00,
  };
  TRY(i2c_testutils_write(i2c, kDeviceAddr, sizeof(kAddr), kAddr, true));
  TRY(i2c_testutils_read(i2c, kDeviceAddr, sizeof(read_data), read_data,
                         kDefaultTimeoutMicros));

  // Check the written bytes match what we wrote.
  TRY_CHECK_ARRAYS_EQ(read_data, data + 2, sizeof(read_data));

  // Erase the values we just wrote to prevent the success state persisting to
  // subsequent runs of the test.
  memset(&data[2], 0xFF, sizeof(read_data));
  TRY(i2c_testutils_write(i2c, kDeviceAddr, sizeof(data), data, false));
  TRY(poll_while_busy(i2c));
  TRY(i2c_testutils_write(i2c, kDeviceAddr, sizeof(kAddr), kAddr, true));
  TRY(i2c_testutils_read(i2c, kDeviceAddr, sizeof(read_data), read_data,
                         kDefaultTimeoutMicros));

  // Check the over-written bytes match the new erased value.
  TRY_CHECK_ARRAYS_EQ(read_data, data + 2, sizeof(read_data));

  return OK_STATUS();
}

static status_t write_read_page_with_irq(dif_i2c_t *i2c) {
  TRY(dif_i2c_irq_acknowledge_all(i2c));
  TRY(dif_i2c_set_watermarks(i2c, /*rx_level=*/kDifI2cLevel4Byte,
                             /*fmt_level=*/kDifI2cLevel4Byte));

  TRY(write_read_page(i2c));

  TRY(check_irq(i2c, kDifI2cIrqFmtThreshold));
  return check_irq(i2c, kDifI2cIrqRxThreshold);
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

bool test_main(void) {
  dif_pinmux_t pinmux;
  dif_i2c_t i2c;
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  i2c_pinmux_platform_id_t platform = I2cPinmuxPlatformIdCw310Pmod;
  status_t test_result = OK_STATUS();
  for (uint8_t i2c_instance = 0; i2c_instance < 3; ++i2c_instance) {
    LOG_INFO("Testing i2c%d", i2c_instance);
    CHECK_STATUS_OK(i2c_configure(&i2c, &pinmux, i2c_instance, platform));

    dif_i2c_speed_t kSpeeds[] = {kDifI2cSpeedStandard, kDifI2cSpeedFast,
                                 kDifI2cSpeedFastPlus};

    for (size_t i = 0; i < ARRAYSIZE(kSpeeds); ++i) {
      CHECK_STATUS_OK(i2c_testutils_set_speed(&i2c, kSpeeds[i]));
      EXECUTE_TEST(test_result, write_read_random, &i2c);
      EXECUTE_TEST(test_result, write_read_page, &i2c);
      EXECUTE_TEST(test_result, write_read_page_with_irq, &i2c);
    }
    CHECK_STATUS_OK(test_shutdown(&i2c, &pinmux, i2c_instance));
  }

  return status_ok(test_result);
}
