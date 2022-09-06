// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/i2c_testutils.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "i2c_regs.h"  // Generated.

static const uint8_t kI2cWrite = 0;
static const uint8_t kI2cRead = 1;

// Default flags for i2c operations.
static const dif_i2c_fmt_flags_t kDefaultFlags = {.start = false,
                                                  .stop = false,
                                                  .read = false,
                                                  .read_cont = false,
                                                  .suppress_nak_irq = false};

void i2c_testutils_wr(dif_i2c_t *i2c, uint8_t addr, uint8_t byte_count,
                      uint8_t *data, bool skip_stop) {
  dif_i2c_fmt_flags_t flags = kDefaultFlags;
  uint8_t data_frame;

  // TODO: The current function does not support write payloads
  // larger than the fifo depth.
  CHECK(byte_count < I2C_PARAM_FIFO_DEPTH);

  // First write the address.
  flags.start = true;
  data_frame = (addr << 1) | kI2cWrite;
  CHECK_DIF_OK(dif_i2c_write_byte_raw(i2c, data_frame, flags));

  // Once address phase is through, blast the rest as generic data.
  flags = kDefaultFlags;
  for (uint8_t i = 0; i < byte_count; ++i) {
    // Issue a stop for the last byte.
    flags.stop = ((i == byte_count - 1) && !skip_stop);
    CHECK_DIF_OK(dif_i2c_write_byte_raw(i2c, data[i], flags));
  }

  // TODO: Check for errors / status.
}

void i2c_testutils_rd(dif_i2c_t *i2c, uint8_t addr, uint8_t byte_count) {
  dif_i2c_fmt_flags_t flags = kDefaultFlags;
  uint8_t data_frame;
  uint8_t fifo_level;

  // First write the address.
  flags.start = true;
  data_frame = (addr << 1) | kI2cRead;
  CHECK_DIF_OK(dif_i2c_write_byte_raw(i2c, data_frame, flags));

  // Once address phase is through, issue the read transaction.
  flags = kDefaultFlags;
  flags.read = true;
  flags.stop = true;

  // Inform the controller how many bytes to read overall.
  CHECK_DIF_OK(dif_i2c_write_byte_raw(i2c, byte_count, flags));

  // TODO: Check for errors / status.
}
