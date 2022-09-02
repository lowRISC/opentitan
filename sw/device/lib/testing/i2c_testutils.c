// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/i2c_testutils.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "i2c_regs.h"  // Generated.

static const uint8_t kI2cWrite = 0;
static const uint8_t kI2cRead = 1;

// default flags
static const dif_i2c_fmt_flags_t default_flags = {.start = false,
                                                  .stop = false,
                                                  .read = false,
                                                  .read_cont = false,
                                                  .suppress_nak_irq = false};

void i2c_testutils_wr(dif_i2c_t *i2c, uint8_t addr, uint8_t byte_count,
                      uint8_t *data, bool skip_stop) {
  dif_i2c_fmt_flags_t flags = default_flags;
  uint8_t data_frame;

  // need a max check for byte_count right now

  // first write the address
  flags.start = true;
  LOG_INFO("testutils: address %d address %d", addr, addr < 1);
  data_frame = (addr << 1) | kI2cWrite;
  CHECK_DIF_OK(dif_i2c_write_byte_raw(i2c, data_frame, flags));

  // once address phase is through, blast the rest as generic data
  flags = default_flags;
  for (uint8_t i = 0; i < byte_count; i++) {
    // issue a stop for the last byte
    if ((i == byte_count - 1) & !skip_stop) {
      flags.stop = true;
    }
    CHECK_DIF_OK(dif_i2c_write_byte_raw(i2c, *data, flags));
    data++;
  }

  // TODO check for errors / status?
}

void i2c_testutils_rd(dif_i2c_t *i2c, uint8_t addr, uint8_t byte_count) {
  dif_i2c_fmt_flags_t flags = default_flags;
  uint8_t data_frame;
  uint8_t fifo_level;

  // need a max check based on FIFO depth
  // for simplicity, don't handle more than FIFO depth right now

  // first write the address
  flags.start = true;
  data_frame = (addr << 1) | kI2cRead;
  CHECK_DIF_OK(dif_i2c_write_byte_raw(i2c, data_frame, flags));

  // once address phase is through, issue the read transaction
  flags = default_flags;
  flags.read = true;
  flags.stop = true;

  // inform the controller how many bytes to read overall
  CHECK_DIF_OK(dif_i2c_write_byte_raw(i2c, byte_count, flags));

  // TODO check for errors / status?
}
