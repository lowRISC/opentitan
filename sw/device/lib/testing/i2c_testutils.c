// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/i2c_testutils.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "hw/top/dt/i2c.h"
#include "hw/top/dt/pinmux.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top/i2c_regs.h"  // Generated.

#define MODULE_ID MAKE_MODULE_ID('i', 'i', 't')

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

/**
 * Get the I2C instance from index.
 *
 * @param i2c_idx I2C index (0-based).
 * @return I2C DT instance, or kDtI2cCount if invalid.
 */
static dt_i2c_t get_i2c_instance(uint8_t i2c_idx) {
  if (i2c_idx >= kDtI2cCount) {
    return kDtI2cCount;
  }
  return (dt_i2c_t)i2c_idx;
}

/**
 * Get the appropriate pads for an I2C instance and platform based on the
 * platform. This replicates the original behavior with different mappings for
 * different platforms.
 *
 * @param i2c_dt I2C DT instance.
 * @param platform The platform to connect the I2C to.
 * @param sda_pad Output parameter for SDA pad.
 * @param scl_pad Output parameter for SCL pad.
 * @return OK_STATUS if successful, error status otherwise.
 */
static status_t get_i2c_pads_for_platform(dt_i2c_t i2c_dt,
                                          i2c_pinmux_platform_id_t platform,
                                          dt_pad_t *sda_pad,
                                          dt_pad_t *scl_pad) {
#if defined(OPENTITAN_IS_DARJEELING)
  // Darjeeling only has I2C0 and uses dedicated pads
  if (i2c_dt != kDtI2c0) {
    return INVALID_ARGUMENT();
  }
  *sda_pad = kDtPadI2c0Sda;
  *scl_pad = kDtPadI2c0Scl;
#elif defined(OPENTITAN_IS_EARLGREY) || defined(OPENTITAN_IS_ENGLISHBREAKFAST)
  // For Earlgrey and EnglishBreakfast platforms
  switch (platform) {
    case I2cPinmuxPlatformIdHyper310:  // CW310 HyperDebug
      *sda_pad = kDtPadIoa7;
      *scl_pad = kDtPadIoa8;
      break;
    case I2cPinmuxPlatformIdDvsim:  // DV
      // In DV, there's one agent for each I2C instance, with a fixed set of
      // muxed pins.
      switch (i2c_dt) {
        case kDtI2c0:  // I2C0 uses the same pins as CW310 HyperDebug
          *sda_pad = kDtPadIoa7;
          *scl_pad = kDtPadIoa8;
          break;
        case kDtI2c1:
          *sda_pad = kDtPadIob10;
          *scl_pad = kDtPadIob9;
          break;
        case kDtI2c2:  // I2C2 uses the same pins as CW310 PMOD
          *sda_pad = kDtPadIob12;
          *scl_pad = kDtPadIob11;
          break;
        default:
          return INVALID_ARGUMENT();
      }
      break;
    case I2cPinmuxPlatformIdCw310Pmod:  // CW310 PMOD
      *sda_pad = kDtPadIob12;
      *scl_pad = kDtPadIob11;
      break;
    default:
      return INVALID_ARGUMENT();
  }
#else
  return UNIMPLEMENTED();
#endif

  return OK_STATUS();
}

status_t i2c_testutils_write(const dif_i2c_t *i2c, uint8_t addr,
                             size_t byte_count, const uint8_t *data,
                             bool skip_stop) {
  dif_i2c_fmt_flags_t flags = kDefaultFlags;
  uint8_t data_frame;

  TRY_CHECK(byte_count > 0);

  // First write the address.
  flags.start = true;
  data_frame = (uint8_t)(addr << 1) | (uint8_t)kI2cWrite;
  TRY(dif_i2c_write_byte_raw(i2c, data_frame, flags));

  // Once address phase is through, blast the rest as generic data.
  flags = kDefaultFlags;
  if (byte_count > 1) {
    TRY(dif_i2c_write_bytes_raw(i2c, byte_count - 1, data, flags));
  }
  // Issue a stop for the last byte.
  flags.stop = !skip_stop;
  TRY(dif_i2c_write_byte_raw(i2c, data[byte_count - 1], flags));

  // TODO: Check for errors / status.
  return OK_STATUS();
}

status_t i2c_testutils_issue_read(const dif_i2c_t *i2c, uint8_t addr,
                                  uint8_t byte_count) {
  dif_i2c_fmt_flags_t flags = kDefaultFlags;
  uint8_t data_frame;
  // The current function doesn't check for space in the FIFOs

  // First, issue a write the address transaction.
  flags.start = true;
  data_frame = (uint8_t)(addr << 1) | (uint8_t)kI2cRead;
  TRY(dif_i2c_write_byte_raw(i2c, data_frame, flags));

  TRY(i2c_testutils_wait_transaction_finish(i2c));
  dif_i2c_controller_halt_events_t halt_events = {0};
  TRY(dif_i2c_get_controller_halt_events(i2c, &halt_events));
  if (!halt_events.nack_received) {
    // We got an ack, schedule the read transaction.
    flags = kDefaultFlags;
    flags.read = true;
    flags.stop = true;
    // Inform the controller how many bytes to read overall.
    TRY(dif_i2c_write_byte_raw(i2c, byte_count, flags));
  } else {
    // We got a nack, clear the irq and return. The caller may retry later.
    TRY(dif_i2c_reset_fmt_fifo(i2c));
    TRY(dif_i2c_clear_controller_halt_events(i2c, halt_events));
    // Force Stop to be sent after the unexpected NACK.
    TRY(dif_i2c_host_set_enabled(i2c, kDifToggleDisabled));
    TRY(dif_i2c_host_set_enabled(i2c, kDifToggleEnabled));
  }
  return OK_STATUS(halt_events.nack_received);
}

status_t i2c_testutils_read(const dif_i2c_t *i2c, uint8_t addr,
                            size_t byte_count, uint8_t *data, size_t timeout) {
  uint32_t nak_count = 0;
  ibex_timeout_t timer = ibex_timeout_init(timeout);

  // Make sure to start from a clean state.
  dif_i2c_controller_halt_events_t halt_events = {0};
  TRY(dif_i2c_get_controller_halt_events(i2c, &halt_events));
  TRY(dif_i2c_clear_controller_halt_events(i2c, halt_events));
  TRY(dif_i2c_reset_rx_fifo(i2c));
  do {
    // Per chunk, as many bytes as fit into the RX FIFO could be transferred.
    // However, as the number of bytes has to be communicated to the target in
    // one byte, UINT8_MAX is another upper limit.
    size_t max_chunk =
        I2C_PARAM_FIFO_DEPTH < UINT8_MAX ? I2C_PARAM_FIFO_DEPTH : UINT8_MAX;
    uint8_t chunk = (uint8_t)(byte_count < max_chunk ? byte_count : max_chunk);

    // Loop until we get an ACK from the device or a timeout.
    while (TRY(i2c_testutils_issue_read(i2c, addr, chunk))) {
      nak_count++;
      if (ibex_timeout_check(&timer)) {
        return DEADLINE_EXCEEDED();
      }
    }

    if (chunk > 0) {
      TRY(dif_i2c_read_bytes(i2c, chunk, data));
      data += chunk;
      byte_count -= chunk;
    }
  } while (byte_count > 0);

  TRY(i2c_testutils_wait_transaction_finish(i2c));
  return OK_STATUS((int32_t)nak_count);
}

status_t i2c_testutils_target_check_start(const dif_i2c_t *i2c, uint8_t *addr) {
  dif_i2c_level_t acq_fifo_lvl;
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
  dif_i2c_level_t acq_fifo_lvl;
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

status_t i2c_testutils_target_read(const dif_i2c_t *i2c, uint16_t byte_count,
                                   const uint8_t *data) {
  dif_i2c_level_t tx_fifo_lvl, acq_fifo_lvl;
  TRY(dif_i2c_get_fifo_levels(i2c, NULL, NULL, &tx_fifo_lvl, &acq_fifo_lvl));
  // Check there's space in tx_fifo and acq_fifo
  TRY_CHECK(tx_fifo_lvl + byte_count <= I2C_PARAM_FIFO_DEPTH);
  TRY_CHECK(acq_fifo_lvl + 2 <= I2C_PARAM_FIFO_DEPTH);

  for (uint16_t i = 0; i < byte_count; ++i) {
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

status_t i2c_testutils_target_write(const dif_i2c_t *i2c, uint16_t byte_count) {
  dif_i2c_level_t acq_fifo_lvl;
  TRY(dif_i2c_get_fifo_levels(i2c, NULL, NULL, NULL, &acq_fifo_lvl));
  TRY_CHECK(acq_fifo_lvl + 2 + byte_count <= I2C_PARAM_FIFO_DEPTH);

  // TODO: Check for errors / status.
  return OK_STATUS();
}

status_t i2c_testutils_target_check_write(const dif_i2c_t *i2c,
                                          uint16_t byte_count, uint8_t *addr,
                                          uint8_t *bytes, uint8_t *cont_byte) {
  dif_i2c_level_t acq_fifo_lvl;
  TRY(dif_i2c_get_fifo_levels(i2c, NULL, NULL, NULL, &acq_fifo_lvl));
  TRY_CHECK(acq_fifo_lvl >= 2 + byte_count);

  int32_t dir = TRY(i2c_testutils_target_check_start(i2c, addr));
  TRY_CHECK(dir == kI2cWrite);

  for (uint16_t i = 0; i < byte_count; ++i) {
    dif_i2c_signal_t signal;
    TRY(dif_i2c_acquire_byte(i2c, bytes + i, &signal));
    TRY_CHECK(signal == kDifI2cSignalNone);
  }

  // TODO: Check for errors / status.

  return i2c_testutils_target_check_end(i2c, cont_byte);
}

status_t i2c_testutils_select_pinmux(const dif_pinmux_t *pinmux, uint8_t i2c_id,
                                     i2c_pinmux_platform_id_t platform) {
  TRY_CHECK(platform < I2cPinmuxPlatformIdCount, "Platform out of bounds");

  dt_i2c_t i2c_dt = get_i2c_instance(i2c_id);
  TRY_CHECK(i2c_dt < kDtI2cCount, "I2C index out of bounds");

  // Get peripheral I/O descriptions for SDA and SCL
  dt_periph_io_t sda_periph_io = dt_i2c_periph_io(i2c_dt, kDtI2cPeriphIoSda);
  dt_periph_io_t scl_periph_io = dt_i2c_periph_io(i2c_dt, kDtI2cPeriphIoScl);

  // Get the appropriate pads for this I2C instance and platform
  dt_pad_t sda_pad, scl_pad;
  TRY(get_i2c_pads_for_platform(i2c_dt, platform, &sda_pad, &scl_pad));

  // Connect SDA and SCL using pinmux testutils
  TRY(pinmux_testutils_connect(pinmux, sda_periph_io, kDtPeriphIoDirInout,
                               sda_pad));
  TRY(pinmux_testutils_connect(pinmux, scl_periph_io, kDtPeriphIoDirInout,
                               scl_pad));

  return OK_STATUS();
}

status_t i2c_testutils_detach_pinmux(const dif_pinmux_t *pinmux,
                                     uint8_t i2c_id) {
  dt_i2c_t i2c_dt = get_i2c_instance(i2c_id);
  TRY_CHECK(i2c_dt < kDtI2cCount, "I2C index out of bounds");

  // Get peripheral I/O descriptions for SDA and SCL
  dt_periph_io_t sda_periph_io = dt_i2c_periph_io(i2c_dt, kDtI2cPeriphIoSda);
  dt_periph_io_t scl_periph_io = dt_i2c_periph_io(i2c_dt, kDtI2cPeriphIoScl);

  // Disconnect SDA and SCL inputs by connecting to constant zero
  TRY(pinmux_testutils_connect(pinmux, sda_periph_io, kDtPeriphIoDirIn,
                               kDtPadConstantZero));
  TRY(pinmux_testutils_connect(pinmux, scl_periph_io, kDtPeriphIoDirIn,
                               kDtPadConstantZero));

  return OK_STATUS();
}

status_t i2c_testutils_set_speed(const dif_i2c_t *i2c, dif_i2c_speed_t speed,
                                 uint32_t sda_rise_nanos,
                                 uint32_t sda_fall_nanos) {
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
    default:
      break;
  }
  // I2C speed parameters.
  dif_i2c_timing_config_t timing_config = {
      .lowest_target_device_speed = speed,
      .clock_period_nanos =
          (uint32_t)udiv64_slow(1000000000, kClockFreqPeripheralHz, NULL),
      .sda_rise_nanos = sda_rise_nanos,
      .sda_fall_nanos = sda_fall_nanos,
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

status_t i2c_testutils_wait_host_idle(const dif_i2c_t *i2c) {
  dif_i2c_status_t status;
  do {
    TRY(dif_i2c_get_status(i2c, &status));
  } while (!status.host_idle);
  return OK_STATUS();
}

status_t i2c_testutils_wait_transaction_finish(const dif_i2c_t *i2c) {
  dif_i2c_status_t status;
  bool controller_halted = false;
  do {
    TRY(dif_i2c_irq_is_pending(i2c, kDifI2cIrqControllerHalt,
                               &controller_halted));
    if (controller_halted) {
      return OK_STATUS(1);
    }
    TRY(dif_i2c_get_status(i2c, &status));
  } while (!status.fmt_fifo_empty);
  return OK_STATUS(0);
}
