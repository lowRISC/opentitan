// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_i2c.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "i2c_regs.h"  // Generated

/**
 * Performs a 32-bit integer unsigned division, rounding up. The bottom
 * 16 bits of the result are then returned.
 *
 * As usual, a divisor of 0 is still Undefined Behavior.
 */
static uint16_t round_up_divide(uint32_t a, uint32_t b) {
  const uint32_t result = ((a - 1) / b) + 1;
  return (uint16_t)result;
}

/**
 * Reads i2c status bits from registers
 */
dif_result_t dif_i2c_get_status(const dif_i2c_t *i2c,
                                dif_i2c_status_t *status) {
  if (i2c == NULL || status == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(i2c->base_addr, I2C_CTRL_REG_OFFSET);
  status->enable_host = bitfield_bit32_read(reg, I2C_CTRL_ENABLEHOST_BIT);
  status->enable_target = bitfield_bit32_read(reg, I2C_CTRL_ENABLETARGET_BIT);
  status->line_loopback = bitfield_bit32_read(reg, I2C_CTRL_LLPBK_BIT);
  reg = mmio_region_read32(i2c->base_addr, I2C_STATUS_REG_OFFSET);
  status->fmt_fifo_full = bitfield_bit32_read(reg, I2C_STATUS_FMTFULL_BIT);
  status->rx_fifo_full = bitfield_bit32_read(reg, I2C_STATUS_RXFULL_BIT);
  status->fmt_fifo_empty = bitfield_bit32_read(reg, I2C_STATUS_FMTEMPTY_BIT);
  status->rx_fifo_empty = bitfield_bit32_read(reg, I2C_STATUS_RXEMPTY_BIT);
  status->host_idle = bitfield_bit32_read(reg, I2C_STATUS_HOSTIDLE_BIT);
  status->target_idle = bitfield_bit32_read(reg, I2C_STATUS_TARGETIDLE_BIT);
  status->tx_fifo_full = bitfield_bit32_read(reg, I2C_STATUS_TXFULL_BIT);
  status->acq_fifo_full = bitfield_bit32_read(reg, I2C_STATUS_ACQFULL_BIT);
  status->tx_fifo_empty = bitfield_bit32_read(reg, I2C_STATUS_TXEMPTY_BIT);
  status->acq_fifo_empty = bitfield_bit32_read(reg, I2C_STATUS_ACQEMPTY_BIT);

  return kDifOk;
}

/**
 * Computes default timing parameters for a particular I2C speed, given the
 * clock period, in nanoseconds.
 *
 * Returns an unspecified value for an invalid speed.
 */
static dif_i2c_config_t default_timing_for_speed(dif_i2c_speed_t speed,
                                                 uint32_t clock_period_nanos) {
  // NOTE: All constants below are lifted from Table 10 of the I2C spec.
  // All literal values are given in nanoseconds; we don't bother putting
  // these into constants since they are not used anywhere else.
  switch (speed) {
    case kDifI2cSpeedStandard:
      return (dif_i2c_config_t){
          .scl_time_high_cycles = round_up_divide(4000, clock_period_nanos),
          .scl_time_low_cycles = round_up_divide(4700, clock_period_nanos),
          .start_signal_setup_cycles =
              round_up_divide(4700, clock_period_nanos),
          .start_signal_hold_cycles = round_up_divide(4000, clock_period_nanos),
          .data_signal_setup_cycles = round_up_divide(250, clock_period_nanos),
          .data_signal_hold_cycles = 1,
          .stop_signal_setup_cycles = round_up_divide(4000, clock_period_nanos),
          .stop_signal_hold_cycles = round_up_divide(4700, clock_period_nanos),
      };
    case kDifI2cSpeedFast:
      return (dif_i2c_config_t){
          .scl_time_high_cycles = round_up_divide(600, clock_period_nanos),
          .scl_time_low_cycles = round_up_divide(1300, clock_period_nanos),
          .start_signal_setup_cycles = round_up_divide(600, clock_period_nanos),
          .start_signal_hold_cycles = round_up_divide(600, clock_period_nanos),
          .data_signal_setup_cycles = round_up_divide(100, clock_period_nanos),
          .data_signal_hold_cycles = 1,
          .stop_signal_setup_cycles = round_up_divide(600, clock_period_nanos),
          .stop_signal_hold_cycles = round_up_divide(1300, clock_period_nanos),
      };
    case kDifI2cSpeedFastPlus:
      return (dif_i2c_config_t){
          .scl_time_high_cycles = round_up_divide(260, clock_period_nanos),
          .scl_time_low_cycles = round_up_divide(500, clock_period_nanos),
          .start_signal_setup_cycles = round_up_divide(260, clock_period_nanos),
          .start_signal_hold_cycles = round_up_divide(260, clock_period_nanos),
          .data_signal_setup_cycles = round_up_divide(50, clock_period_nanos),
          .data_signal_hold_cycles = 1,
          .stop_signal_setup_cycles = round_up_divide(260, clock_period_nanos),
          .stop_signal_hold_cycles = round_up_divide(500, clock_period_nanos),
      };
    default:
      return (dif_i2c_config_t){0};
  }
}

static const uint32_t kNanosPerKBaud = 1000000;  // One million.

dif_result_t dif_i2c_compute_timing(dif_i2c_timing_config_t timing_config,
                                    dif_i2c_config_t *config) {
  if (config == NULL) {
    return kDifBadArg;
  }
  uint32_t lowest_target_device_speed_khz;
  switch (timing_config.lowest_target_device_speed) {
    case kDifI2cSpeedStandard:
      lowest_target_device_speed_khz = 100;
      break;
    case kDifI2cSpeedFast:
      lowest_target_device_speed_khz = 400;
      break;
    case kDifI2cSpeedFastPlus:
      lowest_target_device_speed_khz = 1000;
      break;
    default:
      return kDifBadArg;
  }

  // This code follows the algorithm given in
  // https://docs.opentitan.org/hw/ip/i2c/doc/index.html#initialization

  *config = default_timing_for_speed(timing_config.lowest_target_device_speed,
                                     timing_config.clock_period_nanos);

  config->rise_cycles = round_up_divide(timing_config.sda_rise_nanos,
                                        timing_config.clock_period_nanos);
  config->fall_cycles = round_up_divide(timing_config.sda_fall_nanos,
                                        timing_config.clock_period_nanos);

  uint32_t scl_period_nanos = timing_config.scl_period_nanos;
  uint32_t slowest_scl_period_nanos =
      kNanosPerKBaud / lowest_target_device_speed_khz;
  if (scl_period_nanos < slowest_scl_period_nanos) {
    scl_period_nanos = slowest_scl_period_nanos;
  }
  uint16_t scl_period_cycles =
      round_up_divide(scl_period_nanos, timing_config.clock_period_nanos);

  // Lengthen the SCL high period to accommodate the desired SCL period.
  int32_t lengthened_high_cycles = scl_period_cycles -
                                   config->scl_time_low_cycles -
                                   config->rise_cycles - config->fall_cycles;
  if (lengthened_high_cycles > (int32_t)config->scl_time_high_cycles) {
    if (lengthened_high_cycles < 0 || lengthened_high_cycles > UINT16_MAX) {
      return kDifOutOfRange;
    }
    config->scl_time_high_cycles = (uint16_t)lengthened_high_cycles;
  }

  return kDifOk;
}

dif_result_t dif_i2c_configure(const dif_i2c_t *i2c, dif_i2c_config_t config) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  uint32_t timing0 = 0;
  timing0 = bitfield_field32_write(timing0, I2C_TIMING0_THIGH_FIELD,
                                   config.scl_time_high_cycles);
  timing0 = bitfield_field32_write(timing0, I2C_TIMING0_TLOW_FIELD,
                                   config.scl_time_low_cycles);
  mmio_region_write32(i2c->base_addr, I2C_TIMING0_REG_OFFSET, timing0);

  uint32_t timing1 = 0;
  timing1 = bitfield_field32_write(timing1, I2C_TIMING1_T_R_FIELD,
                                   config.rise_cycles);
  timing1 = bitfield_field32_write(timing1, I2C_TIMING1_T_F_FIELD,
                                   config.fall_cycles);
  mmio_region_write32(i2c->base_addr, I2C_TIMING1_REG_OFFSET, timing1);

  uint32_t timing2 = 0;
  timing2 = bitfield_field32_write(timing2, I2C_TIMING2_TSU_STA_FIELD,
                                   config.start_signal_setup_cycles);
  timing2 = bitfield_field32_write(timing2, I2C_TIMING2_THD_STA_FIELD,
                                   config.start_signal_hold_cycles);
  mmio_region_write32(i2c->base_addr, I2C_TIMING2_REG_OFFSET, timing2);

  uint32_t timing3 = 0;
  timing3 = bitfield_field32_write(timing3, I2C_TIMING3_TSU_DAT_FIELD,
                                   config.data_signal_setup_cycles);
  timing3 = bitfield_field32_write(timing3, I2C_TIMING3_THD_DAT_FIELD,
                                   config.data_signal_hold_cycles);
  mmio_region_write32(i2c->base_addr, I2C_TIMING3_REG_OFFSET, timing3);

  uint32_t timing4 = 0;
  timing4 = bitfield_field32_write(timing4, I2C_TIMING4_TSU_STO_FIELD,
                                   config.stop_signal_setup_cycles);
  timing4 = bitfield_field32_write(timing4, I2C_TIMING4_T_BUF_FIELD,
                                   config.stop_signal_hold_cycles);
  mmio_region_write32(i2c->base_addr, I2C_TIMING4_REG_OFFSET, timing4);

  return kDifOk;
}

dif_result_t dif_i2c_reset_rx_fifo(const dif_i2c_t *i2c) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(i2c->base_addr, I2C_FIFO_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, I2C_FIFO_CTRL_RXRST_BIT, true);
  mmio_region_write32(i2c->base_addr, I2C_FIFO_CTRL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_i2c_reset_fmt_fifo(const dif_i2c_t *i2c) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(i2c->base_addr, I2C_FIFO_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, I2C_FIFO_CTRL_FMTRST_BIT, true);
  mmio_region_write32(i2c->base_addr, I2C_FIFO_CTRL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_i2c_reset_tx_fifo(const dif_i2c_t *i2c) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(i2c->base_addr, I2C_FIFO_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, I2C_FIFO_CTRL_TXRST_BIT, true);
  mmio_region_write32(i2c->base_addr, I2C_FIFO_CTRL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_i2c_reset_acq_fifo(const dif_i2c_t *i2c) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(i2c->base_addr, I2C_FIFO_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, I2C_FIFO_CTRL_ACQRST_BIT, true);
  mmio_region_write32(i2c->base_addr, I2C_FIFO_CTRL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_i2c_set_watermarks(const dif_i2c_t *i2c,
                                    dif_i2c_level_t rx_level,
                                    dif_i2c_level_t fmt_level) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  uint32_t rx_level_value;
  switch (rx_level) {
    case kDifI2cLevel1Byte:
      rx_level_value = I2C_FIFO_CTRL_RXILVL_VALUE_RXLVL1;
      break;
    case kDifI2cLevel4Byte:
      rx_level_value = I2C_FIFO_CTRL_RXILVL_VALUE_RXLVL4;
      break;
    case kDifI2cLevel8Byte:
      rx_level_value = I2C_FIFO_CTRL_RXILVL_VALUE_RXLVL8;
      break;
    case kDifI2cLevel16Byte:
      rx_level_value = I2C_FIFO_CTRL_RXILVL_VALUE_RXLVL16;
      break;
    case kDifI2cLevel30Byte:
      rx_level_value = I2C_FIFO_CTRL_RXILVL_VALUE_RXLVL30;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t fmt_level_value;
  switch (fmt_level) {
    case kDifI2cLevel1Byte:
      fmt_level_value = I2C_FIFO_CTRL_FMTILVL_VALUE_FMTLVL1;
      break;
    case kDifI2cLevel4Byte:
      fmt_level_value = I2C_FIFO_CTRL_FMTILVL_VALUE_FMTLVL4;
      break;
    case kDifI2cLevel8Byte:
      fmt_level_value = I2C_FIFO_CTRL_FMTILVL_VALUE_FMTLVL8;
      break;
    case kDifI2cLevel16Byte:
      fmt_level_value = I2C_FIFO_CTRL_FMTILVL_VALUE_FMTLVL16;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t ctrl_value =
      mmio_region_read32(i2c->base_addr, I2C_FIFO_CTRL_REG_OFFSET);
  ctrl_value = bitfield_field32_write(ctrl_value, I2C_FIFO_CTRL_RXILVL_FIELD,
                                      rx_level_value);
  ctrl_value = bitfield_field32_write(ctrl_value, I2C_FIFO_CTRL_FMTILVL_FIELD,
                                      fmt_level_value);
  mmio_region_write32(i2c->base_addr, I2C_FIFO_CTRL_REG_OFFSET, ctrl_value);

  return kDifOk;
}

dif_result_t dif_i2c_host_set_enabled(const dif_i2c_t *i2c,
                                      dif_toggle_t state) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  if (!dif_is_valid_toggle(state)) {
    return kDifBadArg;
  }
  bool flag = dif_toggle_to_bool(state);

  uint32_t reg = mmio_region_read32(i2c->base_addr, I2C_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, I2C_CTRL_ENABLEHOST_BIT, flag);
  mmio_region_write32(i2c->base_addr, I2C_CTRL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_i2c_device_set_enabled(const dif_i2c_t *i2c,
                                        dif_toggle_t state) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  if (!dif_is_valid_toggle(state)) {
    return kDifBadArg;
  }
  bool flag = dif_toggle_to_bool(state);

  uint32_t reg = mmio_region_read32(i2c->base_addr, I2C_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, I2C_CTRL_ENABLETARGET_BIT, flag);
  mmio_region_write32(i2c->base_addr, I2C_CTRL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_i2c_line_loopback_set_enabled(const dif_i2c_t *i2c,
                                               dif_toggle_t state) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  if (!dif_is_valid_toggle(state)) {
    return kDifBadArg;
  }
  bool flag = dif_toggle_to_bool(state);

  uint32_t reg = mmio_region_read32(i2c->base_addr, I2C_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, I2C_CTRL_LLPBK_BIT, flag);
  mmio_region_write32(i2c->base_addr, I2C_CTRL_REG_OFFSET, reg);

  return kDifOk;
}
dif_result_t dif_i2c_override_set_enabled(const dif_i2c_t *i2c,
                                          dif_toggle_t state) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  if (!dif_is_valid_toggle(state)) {
    return kDifBadArg;
  }
  bool flag = dif_toggle_to_bool(state);

  uint32_t reg = mmio_region_read32(i2c->base_addr, I2C_OVRD_REG_OFFSET);
  reg = bitfield_bit32_write(reg, I2C_OVRD_TXOVRDEN_BIT, flag);
  mmio_region_write32(i2c->base_addr, I2C_OVRD_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_i2c_override_drive_pins(const dif_i2c_t *i2c, bool scl,
                                         bool sda) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  uint32_t override_val =
      mmio_region_read32(i2c->base_addr, I2C_OVRD_REG_OFFSET);
  override_val = bitfield_bit32_write(override_val, I2C_OVRD_SCLVAL_BIT, scl);
  override_val = bitfield_bit32_write(override_val, I2C_OVRD_SDAVAL_BIT, sda);
  mmio_region_write32(i2c->base_addr, I2C_OVRD_REG_OFFSET, override_val);

  return kDifOk;
}

dif_result_t dif_i2c_override_sample_pins(const dif_i2c_t *i2c,
                                          uint16_t *scl_samples,
                                          uint16_t *sda_samples) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  uint32_t samples = mmio_region_read32(i2c->base_addr, I2C_VAL_REG_OFFSET);
  if (scl_samples != NULL) {
    *scl_samples =
        (uint16_t)bitfield_field32_read(samples, I2C_VAL_SCL_RX_FIELD);
  }

  if (sda_samples != NULL) {
    *sda_samples =
        (uint16_t)bitfield_field32_read(samples, I2C_VAL_SDA_RX_FIELD);
  }

  return kDifOk;
}

dif_result_t dif_i2c_get_fifo_levels(const dif_i2c_t *i2c,
                                     uint8_t *fmt_fifo_level,
                                     uint8_t *rx_fifo_level,
                                     uint8_t *tx_fifo_level,
                                     uint8_t *acq_fifo_level) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  uint32_t values =
      mmio_region_read32(i2c->base_addr, I2C_FIFO_STATUS_REG_OFFSET);
  if (fmt_fifo_level != NULL) {
    *fmt_fifo_level =
        (uint8_t)bitfield_field32_read(values, I2C_FIFO_STATUS_FMTLVL_FIELD);
  }
  if (rx_fifo_level != NULL) {
    *rx_fifo_level =
        (uint8_t)bitfield_field32_read(values, I2C_FIFO_STATUS_RXLVL_FIELD);
  }
  if (tx_fifo_level != NULL) {
    *tx_fifo_level =
        (uint8_t)bitfield_field32_read(values, I2C_FIFO_STATUS_TXLVL_FIELD);
  }
  if (acq_fifo_level != NULL) {
    *acq_fifo_level =
        (uint8_t)bitfield_field32_read(values, I2C_FIFO_STATUS_ACQLVL_FIELD);
  }

  return kDifOk;
}

dif_result_t dif_i2c_read_byte(const dif_i2c_t *i2c, uint8_t *byte) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  uint32_t values = mmio_region_read32(i2c->base_addr, I2C_RDATA_REG_OFFSET);
  if (byte != NULL) {
    *byte = (uint8_t)bitfield_field32_read(values, I2C_RDATA_RDATA_FIELD);
  }

  return kDifOk;
}

dif_result_t dif_i2c_write_byte_raw(const dif_i2c_t *i2c, uint8_t byte,
                                    dif_i2c_fmt_flags_t flags) {
  if (i2c == NULL) {
    return kDifBadArg;
  }
  // Validate that "write only" flags and "read only" flags are not set
  // simultaneously.
  bool has_write_flags = flags.start || flags.suppress_nak_irq;
  bool has_read_flags = flags.read || flags.read_cont;
  if (has_write_flags && has_read_flags) {
    return kDifBadArg;
  }
  // Also, read_cont requires read.
  if (flags.read_cont && !flags.read) {
    return kDifBadArg;
  }

  uint32_t fmt_byte = 0;
  fmt_byte = bitfield_field32_write(fmt_byte, I2C_FDATA_FBYTE_FIELD, byte);
  fmt_byte = bitfield_bit32_write(fmt_byte, I2C_FDATA_START_BIT, flags.start);
  fmt_byte = bitfield_bit32_write(fmt_byte, I2C_FDATA_STOP_BIT, flags.stop);
  fmt_byte = bitfield_bit32_write(fmt_byte, I2C_FDATA_READ_BIT, flags.read);
  fmt_byte =
      bitfield_bit32_write(fmt_byte, I2C_FDATA_RCONT_BIT, flags.read_cont);
  fmt_byte = bitfield_bit32_write(fmt_byte, I2C_FDATA_NAKOK_BIT,
                                  flags.suppress_nak_irq);
  mmio_region_write32(i2c->base_addr, I2C_FDATA_REG_OFFSET, fmt_byte);

  return kDifOk;
}

dif_result_t dif_i2c_write_byte(const dif_i2c_t *i2c, uint8_t byte,
                                dif_i2c_fmt_t code, bool suppress_nak_irq) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  // Validate that `suppress_nak_irq` has not been mixed with an Rx code.
  if (suppress_nak_irq) {
    switch (code) {
      case kDifI2cFmtRx:
      case kDifI2cFmtRxContinue:
      case kDifI2cFmtRxStop:
        return kDifBadArg;
      default:
        break;
    }
  }

  // Convert the format code into flags.
  dif_i2c_fmt_flags_t flags = {.suppress_nak_irq = suppress_nak_irq};
  switch (code) {
    case kDifI2cFmtStart:
      flags.start = true;
      break;
    case kDifI2cFmtTx:
      break;
    case kDifI2cFmtTxStop:
      flags.stop = true;
      break;
    case kDifI2cFmtRx:
      flags.read = true;
      break;
    case kDifI2cFmtRxContinue:
      flags.read = true;
      flags.read_cont = true;
      break;
    case kDifI2cFmtRxStop:
      flags.read = true;
      flags.stop = true;
      break;
    default:
      return kDifBadArg;
  }

  return dif_i2c_write_byte_raw(i2c, byte, flags);
}

dif_result_t dif_i2c_transmit_byte(const dif_i2c_t *i2c, uint8_t byte) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  uint32_t tx_byte = 0;
  tx_byte = bitfield_field32_write(tx_byte, I2C_TXDATA_TXDATA_FIELD, byte);
  mmio_region_write32(i2c->base_addr, I2C_TXDATA_REG_OFFSET, tx_byte);

  return kDifOk;
}

dif_result_t dif_i2c_acquire_byte(const dif_i2c_t *i2c, uint8_t *byte,
                                  dif_i2c_signal_t *signal) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  uint32_t acq_byte =
      mmio_region_read32(i2c->base_addr, I2C_ACQDATA_REG_OFFSET);
  if (byte != NULL) {
    *byte = (uint8_t)bitfield_field32_read(acq_byte, I2C_ACQDATA_ABYTE_FIELD);
  }
  if (signal != NULL) {
    *signal = bitfield_field32_read(acq_byte, I2C_ACQDATA_SIGNAL_FIELD);
  }
  return kDifOk;
}

dif_result_t dif_i2c_enable_clock_stretching_timeout(const dif_i2c_t *i2c,
                                                     dif_toggle_t enable,
                                                     uint32_t cycles) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  if (!dif_is_valid_toggle(enable)) {
    return kDifBadArg;
  }
  bool flag = dif_toggle_to_bool(enable);

  uint32_t config = 0;
  config = bitfield_bit32_write(config, I2C_TIMEOUT_CTRL_EN_BIT, flag);
  config = bitfield_field32_write(config, I2C_TIMEOUT_CTRL_VAL_FIELD, cycles);
  mmio_region_write32(i2c->base_addr, I2C_TIMEOUT_CTRL_REG_OFFSET, config);
  return kDifOk;
}

dif_result_t dif_i2c_set_device_id(const dif_i2c_t *i2c, dif_i2c_id_t *id0,
                                   dif_i2c_id_t *id1) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  uint32_t config = 0;
  if (id0 != NULL) {
    config = bitfield_field32_write(config, I2C_TARGET_ID_ADDRESS0_FIELD,
                                    id0->address);
    config =
        bitfield_field32_write(config, I2C_TARGET_ID_MASK0_FIELD, id0->mask);
  } else {
    // Don't listen by default
    config = bitfield_field32_write(config, I2C_TARGET_ID_ADDRESS0_FIELD, 0x7f);
  }

  if (id1 != NULL) {
    config = bitfield_field32_write(config, I2C_TARGET_ID_ADDRESS1_FIELD,
                                    id1->address);
    config =
        bitfield_field32_write(config, I2C_TARGET_ID_MASK1_FIELD, id1->mask);
  } else {
    // Don't listen by default
    config = bitfield_field32_write(config, I2C_TARGET_ID_ADDRESS1_FIELD, 0x7f);
  }

  mmio_region_write32(i2c->base_addr, I2C_TARGET_ID_REG_OFFSET, config);
  return kDifOk;
}

dif_result_t dif_i2c_set_host_timeout(const dif_i2c_t *i2c, uint32_t cycles) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(i2c->base_addr, I2C_HOST_TIMEOUT_CTRL_REG_OFFSET, cycles);
  return kDifOk;
}
