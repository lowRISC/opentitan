// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include <assert.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/i2c_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "i2c_regs.h"  // Generated.

static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "This test assumes the target platform is little endian.");

OTTF_DEFINE_TEST_CONFIG();

/*
 * This test runs in QEMU and expects a DS1338 with address
 * `kDsDeviceAddr` and an i2c-echo device with address
 * `kEchoDeviceAddr` on each i2c bus. Use the following
 * flags in QEMU to create these devices:
 *
 * -device ds1338,bus=ot-i2c<0-2>,address=<kDsDeviceAddr>
 * -device i2c-echo,bus=ot-i2c<0-2>,address=<kEchoDeviceAddr>
 */

enum {
  // Address of the DS1338 device on each bus.
  kDsDeviceAddr = 0x77,
  // Start of NVRAM register in DS1338.
  kDsNvramBaseAddr = 0x8,
  // DS1338 NVRAM size.
  kDsNvramSize = 56,
  // Address of our i2c-echo devices on each bus.
  kEchoDeviceAddr = 0x2e,
  // Our address on the I2C bus for target mode.
  kI2cDeviceTargetAddr = 0x43,
  // Arbitrary payload data.
  kPayloadData1 = 0xc8,
  // Arbitrary payload data.
  kPayloadData2 = 0x6b,
  // Read timeout.
  kTimeout = 10000,  // 10 ms
};

static status_t i2c_setup(dif_i2c_t *i2c, uintptr_t base_addr) {
  mmio_region_t region = mmio_region_from_addr(base_addr);
  TRY(dif_i2c_init(region, i2c));
  TRY(dif_i2c_host_set_enabled(i2c, kDifToggleEnabled));
  TRY(dif_i2c_device_set_enabled(i2c, kDifToggleEnabled));
  return OK_STATUS();
}

status_t i2c_ds1338_test(dif_i2c_t *i2c) {
  uint8_t resp[kDsNvramSize] = {0};
  uint8_t i2c_data = kDsNvramBaseAddr;

  // Check NVRAM initially contains all zeroes
  TRY(i2c_testutils_write(i2c, kDsDeviceAddr, sizeof(uint8_t), &i2c_data,
                          true));
  TRY(i2c_testutils_read(i2c, kDsDeviceAddr, ARRAYSIZE(resp), resp, kTimeout));
  for (size_t i = 0; i < ARRAYSIZE(resp); i++) {
    TRY_CHECK(resp[i] == 0, "NVRAM should be all zeroes");
  }

  // Write arbitrary data to NVRAM, with the first byte
  // setting the pointer to the start of NVRAM.
  uint8_t payload[kDsNvramSize + 1] = {0};
  payload[0] = i2c_data;
  for (size_t i = 1; i < ARRAYSIZE(payload); i++) {
    payload[i] = (uint8_t)(i * 5);
  }
  TRY(i2c_testutils_write(i2c, kDsDeviceAddr, ARRAYSIZE(payload), payload,
                          false));

  // Read back NVRAM, expecting it to be the same
  TRY(i2c_testutils_write(i2c, kDsDeviceAddr, sizeof(uint8_t), &i2c_data,
                          true));
  TRY(i2c_testutils_read(i2c, kDsDeviceAddr, ARRAYSIZE(resp), resp, kTimeout));
  TRY_CHECK(memcmp(&payload[1], resp, ARRAYSIZE(resp)) == 0);

  return OK_STATUS();
}

static status_t i2c_echo_test(dif_i2c_t *i2c) {
  dif_i2c_id_t i2c_address = {.address = kI2cDeviceTargetAddr, .mask = 0x7f};
  TRY(dif_i2c_set_device_id(i2c, &i2c_address, NULL));

  // Write our data to the device, consisting of our address
  // on the bus and 2 payload bytes.
  uint8_t data[] = {kI2cDeviceTargetAddr, kPayloadData1, kPayloadData2};
  TRY(i2c_testutils_write(i2c, kEchoDeviceAddr, ARRAYSIZE(data), data, false));
  TRY(i2c_testutils_wait_transaction_finish(i2c));

  // Check the response, expecting our address and write command
  // and a start signal, followed by our two payload bytes,
  // and a stop signal.
  uint8_t acq_data = 0;
  dif_i2c_signal_t sig = kDifI2cSignalNone;
  TRY(dif_i2c_acquire_byte(i2c, &acq_data, &sig));
  TRY_CHECK((acq_data >> 1) == kI2cDeviceTargetAddr, "Unexpected address");
  TRY_CHECK((acq_data & 1) == 0, "Expected write command, got read");
  TRY_CHECK(sig == kDifI2cSignalStart, "Expected START signal");

  TRY(dif_i2c_acquire_byte(i2c, &acq_data, &sig));
  TRY_CHECK(acq_data == kPayloadData1, "Unexpected payload");

  TRY(dif_i2c_acquire_byte(i2c, &acq_data, &sig));
  TRY_CHECK(acq_data == kPayloadData2, "Unexpected payload");

  TRY(dif_i2c_acquire_byte(i2c, &acq_data, &sig));
  TRY_CHECK(sig == kDifI2cSignalStop, "Expected STOP signal");

  TRY(dif_i2c_reset_acq_fifo(i2c));

  return OK_STATUS();
}

bool test_main(void) {
  dif_i2c_t i2cs[3] = {0};

  const uintptr_t kI2cBaseAddrs[3] = {TOP_EARLGREY_I2C0_BASE_ADDR,
                                      TOP_EARLGREY_I2C1_BASE_ADDR,
                                      TOP_EARLGREY_I2C2_BASE_ADDR};

  for (size_t i = 0; i < ARRAYSIZE(i2cs); i++) {
    CHECK_STATUS_OK(i2c_setup(&i2cs[i], kI2cBaseAddrs[i]));
  }

  status_t test_result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(i2cs); i++) {
    EXECUTE_TEST(test_result, i2c_ds1338_test, &i2cs[i]);
    EXECUTE_TEST(test_result, i2c_echo_test, &i2cs[i]);
  }

  return status_ok(test_result);
}
