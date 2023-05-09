// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/i2c_testutils.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "i2c_regs.h"  // Generated.

enum {
  kI2cWrite = 0,
  kI2cRead = 1,
};

// Default flags for i2c operations.
static const dif_i2c_fmt_flags_t kDefaultFlags = {.start = false,
                                                  .stop = false,
                                                  .read = false,
                                                  .read_cont = false,
                                                  .suppress_nak_irq = false};

typedef struct i2c_connect_conf {
  const top_earlgrey_pinmux_mio_out_t pins_mio_out[2];
  const top_earlgrey_pinmux_insel_t pins_insel[2];
  const top_earlgrey_pinmux_peripheral_in_t pins_peripheral_in[2];
  const top_earlgrey_pinmux_outsel_t pins_outsel[2];
} i2c_connect_conf_t;

const i2c_connect_conf_t i2c_conf[] = {
    {.pins_mio_out = {kTopEarlgreyPinmuxMioOutIoa7,
                      kTopEarlgreyPinmuxMioOutIoa8},
     .pins_insel = {kTopEarlgreyPinmuxInselIoa7, kTopEarlgreyPinmuxInselIoa8},
     .pins_peripheral_in =
         {
             kTopEarlgreyPinmuxPeripheralInI2c0Sda,
             kTopEarlgreyPinmuxPeripheralInI2c0Scl,
         },
     .pins_outsel =
         {
             kTopEarlgreyPinmuxOutselI2c0Sda,
             kTopEarlgreyPinmuxOutselI2c0Scl,
         }},
    {.pins_mio_out = {kTopEarlgreyPinmuxMioOutIob9,
                      kTopEarlgreyPinmuxMioOutIob10},
     .pins_insel = {kTopEarlgreyPinmuxInselIob9, kTopEarlgreyPinmuxInselIob10},
     .pins_peripheral_in = {kTopEarlgreyPinmuxPeripheralInI2c1Scl,
                            kTopEarlgreyPinmuxPeripheralInI2c1Sda},
     .pins_outsel = {kTopEarlgreyPinmuxOutselI2c1Scl,
                     kTopEarlgreyPinmuxOutselI2c1Sda}},
    {.pins_mio_out = {kTopEarlgreyPinmuxMioOutIob11,
                      kTopEarlgreyPinmuxMioOutIob12},
     .pins_insel = {kTopEarlgreyPinmuxInselIob11, kTopEarlgreyPinmuxInselIob12},
     .pins_peripheral_in = {kTopEarlgreyPinmuxPeripheralInI2c2Scl,
                            kTopEarlgreyPinmuxPeripheralInI2c2Sda},
     .pins_outsel = {kTopEarlgreyPinmuxOutselI2c2Scl,
                     kTopEarlgreyPinmuxOutselI2c2Sda}}};

status_t i2c_testutils_write(const dif_i2c_t *i2c, uint8_t addr,
                             uint8_t byte_count, const uint8_t *data,
                             bool skip_stop) {
  dif_i2c_fmt_flags_t flags = kDefaultFlags;
  uint8_t data_frame;

  // The current function does not support initializing a write while another
  // transaction is in progress

  // TODO: The current function does not support write payloads
  // larger than the fifo depth.
  TRY_CHECK(byte_count <= I2C_PARAM_FIFO_DEPTH);

  // TODO: #15377 The I2C DIF says: "Callers should prefer
  // `dif_i2c_write_byte()` instead, since that function provides clearer
  // semantics. This function should only really be used for testing or
  // troubleshooting a device.

  // First write the address.
  flags.start = true;
  data_frame = (uint8_t)(addr << 1) | (uint8_t)kI2cWrite;
  TRY(dif_i2c_write_byte_raw(i2c, data_frame, flags));

  // Once address phase is through, blast the rest as generic data.
  flags = kDefaultFlags;
  for (uint8_t i = 0; i < byte_count; ++i) {
    // Issue a stop for the last byte.
    flags.stop = ((i == byte_count - 1) && !skip_stop);
    TRY(dif_i2c_write_byte_raw(i2c, data[i], flags));
  }

  // TODO: Check for errors / status.
  return OK_STATUS();
}

status_t i2c_testutils_issue_read(const dif_i2c_t *i2c, uint8_t addr,
                                  uint8_t byte_count) {
  dif_i2c_fmt_flags_t flags = kDefaultFlags;
  uint8_t data_frame;

  // The current function doesn't check for space in the FIFOs

  // First write the address.
  flags.start = true;
  data_frame = (uint8_t)(addr << 1) | (uint8_t)kI2cRead;
  TRY(dif_i2c_write_byte_raw(i2c, data_frame, flags));

  // Schedule the read transaction by writing flags to the fifo.
  flags = kDefaultFlags;
  flags.read = true;
  flags.stop = true;

  // Inform the controller how many bytes to read overall.
  TRY(dif_i2c_write_byte_raw(i2c, byte_count, flags));

  // TODO: Check for errors / status.
  return OK_STATUS();
}

status_t i2c_testutils_fifo_empty(const dif_i2c_t *i2c) {
  dif_i2c_status_t status;
  TRY(dif_i2c_get_status(i2c, &status));
  return OK_STATUS(status.rx_fifo_empty);
}

status_t i2c_testutils_read(const dif_i2c_t *i2c, uint8_t addr,
                            uint8_t byte_count, uint8_t *data) {
  TRY(i2c_testutils_issue_read(i2c, addr, byte_count));

  while (byte_count-- != 0) {
    IBEX_TRY_SPIN_FOR(TRY(i2c_testutils_fifo_empty(i2c)) == false, 5000);
    TRY(dif_i2c_read_byte(i2c, data++));
  }

  return OK_STATUS();
}

status_t i2c_testutils_target_check_start(const dif_i2c_t *i2c, uint8_t *addr) {
  uint8_t acq_fifo_lvl;
  TRY(dif_i2c_get_fifo_levels(i2c, NULL, NULL, NULL, &acq_fifo_lvl));
  TRY_CHECK(acq_fifo_lvl > 1);

  dif_i2c_signal_t signal;
  uint8_t byte;
  TRY(dif_i2c_acquire_byte(i2c, &byte, &signal));
  // Check acq_fifo is as expected and write addr and continue
  TRY_CHECK(signal == kDifI2cSignalStart);
  *addr = byte >> 1;

  return OK_STATUS(byte & kI2cRead);
}

status_t i2c_testutils_target_check_end(const dif_i2c_t *i2c,
                                        uint8_t *cont_byte) {
  uint8_t acq_fifo_lvl;
  TRY(dif_i2c_get_fifo_levels(i2c, NULL, NULL, NULL, &acq_fifo_lvl));
  TRY_CHECK(acq_fifo_lvl >= 1);

  dif_i2c_signal_t signal;
  uint8_t byte;
  TRY(dif_i2c_acquire_byte(i2c, &byte, &signal));
  // Check transaction is terminated with a stop or a continue that the caller
  // is prepared to handle
  if (signal == kDifI2cSignalStop) {
    return OK_STATUS(false);
  }
  TRY_CHECK(cont_byte != NULL);
  *cont_byte = byte;
  TRY_CHECK(signal == kDifI2cSignalRepeat);

  return OK_STATUS(true);
}

status_t i2c_testutils_target_read(const dif_i2c_t *i2c, uint8_t byte_count,
                                   const uint8_t *data) {
  uint8_t tx_fifo_lvl, acq_fifo_lvl;
  TRY(dif_i2c_get_fifo_levels(i2c, NULL, NULL, &tx_fifo_lvl, &acq_fifo_lvl));
  // Check there's space in tx_fifo and acq_fifo
  TRY_CHECK(tx_fifo_lvl + byte_count <= I2C_PARAM_FIFO_DEPTH);
  TRY_CHECK(acq_fifo_lvl + 2 <= I2C_PARAM_FIFO_DEPTH);

  for (uint8_t i = 0; i < byte_count; ++i) {
    TRY(dif_i2c_transmit_byte(i2c, data[i]));
  }
  // TODO: Check for errors / status.
  return OK_STATUS();
}

status_t i2c_testutils_target_check_read(const dif_i2c_t *i2c, uint8_t *addr,
                                         uint8_t *cont_byte) {
  int32_t dir = TRY(i2c_testutils_target_check_start(i2c, addr));
  TRY_CHECK(dir == kI2cRead);
  // TODO: Check for errors / status.
  return i2c_testutils_target_check_end(i2c, cont_byte);
}

status_t i2c_testutils_target_write(const dif_i2c_t *i2c, uint8_t byte_count) {
  uint8_t acq_fifo_lvl;
  TRY(dif_i2c_get_fifo_levels(i2c, NULL, NULL, NULL, &acq_fifo_lvl));
  TRY_CHECK(acq_fifo_lvl + 2 + byte_count <= I2C_PARAM_FIFO_DEPTH);

  // TODO: Check for errors / status.
  return OK_STATUS();
}

status_t i2c_testutils_target_check_write(const dif_i2c_t *i2c,
                                          uint8_t byte_count, uint8_t *addr,
                                          uint8_t *bytes, uint8_t *cont_byte) {
  uint8_t acq_fifo_lvl;
  TRY(dif_i2c_get_fifo_levels(i2c, NULL, NULL, NULL, &acq_fifo_lvl));
  TRY_CHECK(acq_fifo_lvl >= 2 + byte_count);

  int32_t dir = TRY(i2c_testutils_target_check_start(i2c, addr));
  TRY_CHECK(dir == kI2cWrite);

  for (uint8_t i = 0; i < byte_count; ++i) {
    dif_i2c_signal_t signal;
    TRY(dif_i2c_acquire_byte(i2c, bytes + i, &signal));
    TRY_CHECK(signal == kDifI2cSignalNone);
  }

  // TODO: Check for errors / status.

  return i2c_testutils_target_check_end(i2c, cont_byte);
}

status_t i2c_testutils_connect_i2c_to_pinmux_pins(const dif_pinmux_t *pinmux,
                                                  uint8_t kI2cIdx) {
  TRY(dif_pinmux_input_select(pinmux, i2c_conf[kI2cIdx].pins_peripheral_in[0],
                              i2c_conf[kI2cIdx].pins_insel[0]));
  TRY(dif_pinmux_input_select(pinmux, i2c_conf[kI2cIdx].pins_peripheral_in[1],
                              i2c_conf[kI2cIdx].pins_insel[1]));
  TRY(dif_pinmux_output_select(pinmux, i2c_conf[kI2cIdx].pins_mio_out[0],
                               i2c_conf[kI2cIdx].pins_outsel[0]));
  TRY(dif_pinmux_output_select(pinmux, i2c_conf[kI2cIdx].pins_mio_out[1],
                               i2c_conf[kI2cIdx].pins_outsel[1]));
  return OK_STATUS();
}

status_t i2c_testutils_set_speed(const dif_i2c_t *i2c, dif_i2c_speed_t speed) {
  uint32_t speed_khz = 0;
  switch (speed) {
    case kDifI2cSpeedStandard:
      LOG_INFO("Setting i2c to %s mode.", "Standard (100kHz)");
      speed_khz = 100;
      break;
    case kDifI2cSpeedFast:
      LOG_INFO("Setting i2c to %s mode.", "Fast (400kHz)");
      speed_khz = 400;
      break;
    case kDifI2cSpeedFastPlus:
      LOG_INFO("Setting i2c to %s mode.", "FastPlus (1000kHz)");
      speed_khz = 1000;
      break;
  }
  // I2C speed parameters.
  dif_i2c_timing_config_t timing_config = {
      .lowest_target_device_speed = speed,
      .clock_period_nanos =
          (uint32_t)udiv64_slow(1000000000, kClockFreqPeripheralHz, NULL),
      .sda_rise_nanos = 400,
      .sda_fall_nanos = 110,
      .scl_period_nanos = 1000000 / speed_khz};

  dif_i2c_status_t status;
  TRY(dif_i2c_get_status(i2c, &status));
  if (status.enable_host) {
    TRY(dif_i2c_host_set_enabled(i2c, kDifToggleDisabled));
  }
  dif_i2c_config_t config;
  TRY(dif_i2c_compute_timing(timing_config, &config));

  LOG_INFO("period:%d nanos, cycles={fall=%d, rise=%d, hi=%d, lo=%d}",
           timing_config.clock_period_nanos, config.fall_cycles,
           config.rise_cycles, config.scl_time_high_cycles,
           config.scl_time_low_cycles);

  TRY(dif_i2c_configure(i2c, config));
  // Reenable if it was enabled before.
  if (status.enable_host) {
    TRY(dif_i2c_host_set_enabled(i2c, kDifToggleEnabled));
  }

  return OK_STATUS();
}
