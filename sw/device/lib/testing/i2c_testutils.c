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

  // The current function does not support initializing a write while another
  // transaction is in progress

  // TODO: The current function does not support write payloads
  // larger than the fifo depth.
  CHECK(byte_count < I2C_PARAM_FIFO_DEPTH);

  // TODO: #15377 The I2C DIF says: "Callers should prefer
  // `dif_i2c_write_byte()` instead, since that function provides clearer
  // semantics. This function should only really be used for testing or
  // troubleshooting a device.

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

  // The current function doesn't check for space in the FIFOs

  // First write the address.
  flags.start = true;
  data_frame = (addr << 1) | kI2cRead;
  CHECK_DIF_OK(dif_i2c_write_byte_raw(i2c, data_frame, flags));

  // Schedule the read transaction by writing flags to the fifo.
  flags = kDefaultFlags;
  flags.read = true;
  flags.stop = true;

  // Inform the controller how many bytes to read overall.
  CHECK_DIF_OK(dif_i2c_write_byte_raw(i2c, byte_count, flags));

  // TODO: Check for errors / status.
}

bool i2c_testutils_target_check_start(dif_i2c_t *i2c, uint8_t *addr) {
  uint8_t acq_fifo_lvl;
  CHECK_DIF_OK(dif_i2c_get_fifo_levels(i2c, NULL, NULL, NULL, &acq_fifo_lvl));
  CHECK(acq_fifo_lvl > 1);

  dif_i2c_signal_t signal;
  uint8_t byte;
  CHECK_DIF_OK(dif_i2c_acquire_byte(i2c, &byte, &signal));
  // Check acq_fifo is as expected and write addr and continue
  CHECK(signal == kDifI2cSignalStart);
  *addr = byte >> 1;
  return byte & kI2cRead;
}

bool i2c_testutils_target_check_end(dif_i2c_t *i2c, uint8_t *cont_byte) {
  uint8_t acq_fifo_lvl;
  CHECK_DIF_OK(dif_i2c_get_fifo_levels(i2c, NULL, NULL, NULL, &acq_fifo_lvl));
  CHECK(acq_fifo_lvl > 1);

  dif_i2c_signal_t signal;
  uint8_t byte;
  CHECK_DIF_OK(dif_i2c_acquire_byte(i2c, &byte, &signal));
  // Check transaction is terminated with a stop or a continue that the caller
  // is prepared to handle
  if (signal == kDifI2cSignalStop) {
    return false;
  }
  CHECK(cont_byte != NULL);
  *cont_byte = byte;
  CHECK(signal == kDifI2cSignalRepeat);
  return true;
}

void i2c_testutils_target_rd(dif_i2c_t *i2c, uint8_t byte_count,
                             uint8_t *data) {
  uint8_t tx_fifo_lvl, acq_fifo_lvl;
  CHECK_DIF_OK(
      dif_i2c_get_fifo_levels(i2c, NULL, NULL, &tx_fifo_lvl, &acq_fifo_lvl));
  // Check there's space in tx_fifo and acq_fifo
  CHECK(tx_fifo_lvl + byte_count <= I2C_PARAM_FIFO_DEPTH);
  CHECK(acq_fifo_lvl + 2 <= I2C_PARAM_FIFO_DEPTH);

  for (uint8_t i = 0; i < byte_count; ++i) {
    CHECK_DIF_OK(dif_i2c_transmit_byte(i2c, data[i]));
  }
  // TODO: Check for errors / status.
}

bool i2c_testutils_target_check_rd(dif_i2c_t *i2c, uint8_t *addr,
                                   uint8_t *cont_byte) {
  CHECK(i2c_testutils_target_check_start(i2c, addr) == kI2cRead);
  // TODO: Check for errors / status.
  return i2c_testutils_target_check_end(i2c, cont_byte);
}

void i2c_testutils_target_wr(dif_i2c_t *i2c, uint8_t byte_count) {
  uint8_t acq_fifo_lvl;
  CHECK_DIF_OK(dif_i2c_get_fifo_levels(i2c, NULL, NULL, NULL, &acq_fifo_lvl));
  CHECK(acq_fifo_lvl + 2 + byte_count <= I2C_PARAM_FIFO_DEPTH);

  // TODO: Check for errors / status.
}

bool i2c_testutils_target_check_wr(dif_i2c_t *i2c, uint8_t byte_count,
                                   uint8_t *addr, uint8_t *bytes,
                                   uint8_t *cont_byte) {
  uint8_t acq_fifo_lvl;
  CHECK_DIF_OK(dif_i2c_get_fifo_levels(i2c, NULL, NULL, NULL, &acq_fifo_lvl));
  CHECK(acq_fifo_lvl >= 2 + byte_count);

  CHECK(i2c_testutils_target_check_start(i2c, addr) == kI2cWrite);

  for (uint8_t i = 0; i < byte_count; ++i) {
    dif_i2c_signal_t signal;
    CHECK_DIF_OK(dif_i2c_acquire_byte(i2c, bytes, &signal));
    CHECK(signal == kDifI2cSignalNone);
  }

  // TODO: Check for errors / status.

  return i2c_testutils_target_check_end(i2c, cont_byte);
}
