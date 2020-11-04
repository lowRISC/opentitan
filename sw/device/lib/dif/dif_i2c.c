// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_i2c.h"

#include "sw/device/lib/base/bitfield.h"
#include "i2c_regs.h"  // Generated

/**
 * Performs a 32-bit integer unsigned division, rounding up. The bottom
 * 16 bits of the result are then returned.
 *
 * As usual, a divisor of 0 is still Undefined Behavior.
 */
static uint16_t round_up_divide(uint32_t a, uint32_t b) {
  if (a == 0) {
    return 0;
  }

  return ((a - 1) / b) + 1;
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
          .data_signal_hold_cycles = 0,
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
          .data_signal_hold_cycles = 0,
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
          .data_signal_hold_cycles = 0,
          .stop_signal_setup_cycles = round_up_divide(260, clock_period_nanos),
          .stop_signal_hold_cycles = round_up_divide(500, clock_period_nanos),
      };
    default:
      return (dif_i2c_config_t){0};
  }
}

static const uint32_t kNanosPerKBaud = 1000000;  // One million.

dif_i2c_result_t dif_i2c_compute_timing(dif_i2c_timing_config_t timing_config,
                                        dif_i2c_config_t *config) {
  if (config == NULL) {
    return kDifI2cBadArg;
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
      return kDifI2cBadArg;
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
  uint16_t lengthened_high_cycles = scl_period_cycles -
                                    config->scl_time_low_cycles -
                                    config->rise_cycles - config->fall_cycles;
  if (lengthened_high_cycles > config->scl_time_high_cycles) {
    config->scl_time_high_cycles = lengthened_high_cycles;
  }

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_init(dif_i2c_params_t params, dif_i2c_t *i2c) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  i2c->params = params;

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_configure(const dif_i2c_t *i2c,
                                   dif_i2c_config_t config) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  uint32_t timing0 = 0;
  timing0 = bitfield_field32_write(timing0, I2C_TIMING0_THIGH_FIELD,
                                   config.scl_time_high_cycles);
  timing0 = bitfield_field32_write(timing0, I2C_TIMING0_TLOW_FIELD,
                                   config.scl_time_low_cycles);
  mmio_region_write32(i2c->params.base_addr, I2C_TIMING0_REG_OFFSET, timing0);

  uint32_t timing1 = 0;
  timing1 = bitfield_field32_write(timing1, I2C_TIMING1_T_R_FIELD,
                                   config.rise_cycles);
  timing1 = bitfield_field32_write(timing1, I2C_TIMING1_T_F_FIELD,
                                   config.fall_cycles);
  mmio_region_write32(i2c->params.base_addr, I2C_TIMING1_REG_OFFSET, timing1);

  uint32_t timing2 = 0;
  timing2 = bitfield_field32_write(timing2, I2C_TIMING2_TSU_STA_FIELD,
                                   config.start_signal_setup_cycles);
  timing2 = bitfield_field32_write(timing2, I2C_TIMING2_THD_STA_FIELD,
                                   config.start_signal_hold_cycles);
  mmio_region_write32(i2c->params.base_addr, I2C_TIMING2_REG_OFFSET, timing2);

  uint32_t timing3 = 0;
  timing3 = bitfield_field32_write(timing3, I2C_TIMING3_TSU_DAT_FIELD,
                                   config.data_signal_setup_cycles);
  timing3 = bitfield_field32_write(timing3, I2C_TIMING3_THD_DAT_FIELD,
                                   config.data_signal_hold_cycles);
  mmio_region_write32(i2c->params.base_addr, I2C_TIMING3_REG_OFFSET, timing3);

  uint32_t timing4 = 0;
  timing4 = bitfield_field32_write(timing4, I2C_TIMING4_TSU_STO_FIELD,
                                   config.stop_signal_setup_cycles);
  timing4 = bitfield_field32_write(timing4, I2C_TIMING4_T_BUF_FIELD,
                                   config.stop_signal_hold_cycles);
  mmio_region_write32(i2c->params.base_addr, I2C_TIMING4_REG_OFFSET, timing4);

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_reset_rx_fifo(const dif_i2c_t *i2c) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  uint32_t reg =
      mmio_region_read32(i2c->params.base_addr, I2C_FIFO_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, I2C_FIFO_CTRL_RXRST_BIT, true);
  mmio_region_write32(i2c->params.base_addr, I2C_FIFO_CTRL_REG_OFFSET, reg);

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_reset_fmt_fifo(const dif_i2c_t *i2c) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  uint32_t reg =
      mmio_region_read32(i2c->params.base_addr, I2C_FIFO_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, I2C_FIFO_CTRL_FMTRST_BIT, true);
  mmio_region_write32(i2c->params.base_addr, I2C_FIFO_CTRL_REG_OFFSET, reg);

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_set_watermarks(const dif_i2c_t *i2c,
                                        dif_i2c_level_t rx_level,
                                        dif_i2c_level_t fmt_level) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  ptrdiff_t rx_level_value;
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
      return kDifI2cBadArg;
  }

  ptrdiff_t fmt_level_value;
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
      return kDifI2cBadArg;
  }

  uint32_t ctrl_value =
      mmio_region_read32(i2c->params.base_addr, I2C_FIFO_CTRL_REG_OFFSET);
  ctrl_value = bitfield_field32_write(ctrl_value, I2C_FIFO_CTRL_RXILVL_FIELD,
                                      rx_level_value);
  ctrl_value = bitfield_field32_write(ctrl_value, I2C_FIFO_CTRL_FMTILVL_FIELD,
                                      fmt_level_value);
  mmio_region_write32(i2c->params.base_addr, I2C_FIFO_CTRL_REG_OFFSET,
                      ctrl_value);

  return kDifI2cOk;
}

DIF_WARN_UNUSED_RESULT
static bool irq_index(dif_i2c_irq_t irq, bitfield_bit32_index_t *bit_index) {
  switch (irq) {
    case kDifI2cIrqFmtWatermarkUnderflow:
      *bit_index = I2C_INTR_COMMON_FMT_WATERMARK_BIT;
      break;
    case kDifI2cIrqRxWatermarkOverflow:
      *bit_index = I2C_INTR_COMMON_RX_WATERMARK_BIT;
      break;
    case kDifI2cIrqFmtFifoOverflow:
      *bit_index = I2C_INTR_COMMON_FMT_OVERFLOW_BIT;
      break;
    case kDifI2cIrqRxFifoOverflow:
      *bit_index = I2C_INTR_COMMON_RX_OVERFLOW_BIT;
      break;
    case kDifI2cIrqNak:
      *bit_index = I2C_INTR_COMMON_NAK_BIT;
      break;
    case kDifI2cIrqSclInterference:
      *bit_index = I2C_INTR_COMMON_SCL_INTERFERENCE_BIT;
      break;
    case kDifI2cIrqSdaInterference:
      *bit_index = I2C_INTR_COMMON_SDA_INTERFERENCE_BIT;
      break;
    case kDifI2cIrqClockStretchTimeout:
      *bit_index = I2C_INTR_COMMON_STRETCH_TIMEOUT_BIT;
      break;
    case kDifI2cIrqSdaUnstable:
      *bit_index = I2C_INTR_COMMON_SDA_UNSTABLE_BIT;
      break;
    default:
      return false;
  }
  return true;
}

dif_i2c_result_t dif_i2c_irq_is_pending(const dif_i2c_t *i2c, dif_i2c_irq_t irq,
                                        bool *is_pending) {
  if (i2c == NULL || is_pending == NULL) {
    return kDifI2cBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(irq, &index)) {
    return kDifI2cBadArg;
  }

  uint32_t reg =
      mmio_region_read32(i2c->params.base_addr, I2C_INTR_STATE_REG_OFFSET);
  *is_pending = bitfield_bit32_read(reg, index);

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_irq_acknowledge(const dif_i2c_t *i2c,
                                         dif_i2c_irq_t irq) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(irq, &index)) {
    return kDifI2cBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(i2c->params.base_addr, I2C_INTR_STATE_REG_OFFSET, reg);

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_irq_get_enabled(const dif_i2c_t *i2c,
                                         dif_i2c_irq_t irq,
                                         dif_i2c_toggle_t *state) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(irq, &index)) {
    return kDifI2cBadArg;
  }

  uint32_t reg =
      mmio_region_read32(i2c->params.base_addr, I2C_INTR_ENABLE_REG_OFFSET);
  bool is_enabled = bitfield_bit32_read(reg, index);
  *state = is_enabled ? kDifI2cToggleEnabled : kDifI2cToggleDisabled;

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_irq_set_enabled(const dif_i2c_t *i2c,
                                         dif_i2c_irq_t irq,
                                         dif_i2c_toggle_t state) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(irq, &index)) {
    return kDifI2cBadArg;
  }

  bool flag;
  switch (state) {
    case kDifI2cToggleEnabled:
      flag = true;
      break;
    case kDifI2cToggleDisabled:
      flag = false;
      break;
    default:
      return kDifI2cBadArg;
  }

  uint32_t reg =
      mmio_region_read32(i2c->params.base_addr, I2C_INTR_ENABLE_REG_OFFSET);
  reg = bitfield_bit32_write(reg, index, flag);
  mmio_region_write32(i2c->params.base_addr, I2C_INTR_ENABLE_REG_OFFSET, reg);

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_irq_force(const dif_i2c_t *i2c, dif_i2c_irq_t irq) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(irq, &index)) {
    return kDifI2cBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(i2c->params.base_addr, I2C_INTR_TEST_REG_OFFSET, reg);

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_irq_disable_all(const dif_i2c_t *i2c,
                                         dif_i2c_irq_snapshot_t *snapshot) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  if (snapshot != NULL) {
    *snapshot =
        mmio_region_read32(i2c->params.base_addr, I2C_INTR_ENABLE_REG_OFFSET);
  }

  mmio_region_write32(i2c->params.base_addr, I2C_INTR_ENABLE_REG_OFFSET, 0);

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_irq_restore_all(
    const dif_i2c_t *i2c, const dif_i2c_irq_snapshot_t *snapshot) {
  if (i2c == NULL || snapshot == NULL) {
    return kDifI2cBadArg;
  }

  mmio_region_write32(i2c->params.base_addr, I2C_INTR_ENABLE_REG_OFFSET,
                      *snapshot);

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_host_set_enabled(const dif_i2c_t *i2c,
                                          dif_i2c_toggle_t state) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  bool flag;
  switch (state) {
    case kDifI2cToggleEnabled:
      flag = true;
      break;
    case kDifI2cToggleDisabled:
      flag = false;
      break;
    default:
      return kDifI2cBadArg;
  }

  uint32_t reg = mmio_region_read32(i2c->params.base_addr, I2C_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, I2C_CTRL_ENABLEHOST_BIT, flag);
  mmio_region_write32(i2c->params.base_addr, I2C_CTRL_REG_OFFSET, reg);

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_override_set_enabled(const dif_i2c_t *i2c,
                                              dif_i2c_toggle_t state) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  bool flag;
  switch (state) {
    case kDifI2cToggleEnabled:
      flag = true;
      break;
    case kDifI2cToggleDisabled:
      flag = false;
      break;
    default:
      return kDifI2cBadArg;
  }

  uint32_t reg = mmio_region_read32(i2c->params.base_addr, I2C_OVRD_REG_OFFSET);
  reg = bitfield_bit32_write(reg, I2C_OVRD_TXOVRDEN_BIT, flag);
  mmio_region_write32(i2c->params.base_addr, I2C_OVRD_REG_OFFSET, reg);

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_override_drive_pins(const dif_i2c_t *i2c, bool scl,
                                             bool sda) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  uint32_t override_val =
      mmio_region_read32(i2c->params.base_addr, I2C_OVRD_REG_OFFSET);
  override_val = bitfield_bit32_write(override_val, I2C_OVRD_SCLVAL_BIT, scl);
  override_val = bitfield_bit32_write(override_val, I2C_OVRD_SDAVAL_BIT, sda);
  mmio_region_write32(i2c->params.base_addr, I2C_OVRD_REG_OFFSET, override_val);

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_override_sample_pins(const dif_i2c_t *i2c,
                                              uint16_t *scl_samples,
                                              uint16_t *sda_samples) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  uint32_t samples =
      mmio_region_read32(i2c->params.base_addr, I2C_VAL_REG_OFFSET);
  if (scl_samples != NULL) {
    *scl_samples = bitfield_field32_read(samples, I2C_VAL_SCL_RX_FIELD);
  }

  if (sda_samples != NULL) {
    *sda_samples = bitfield_field32_read(samples, I2C_VAL_SDA_RX_FIELD);
  }

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_get_fifo_levels(const dif_i2c_t *i2c,
                                         uint8_t *fmt_fifo_level,
                                         uint8_t *rx_fifo_level) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  uint32_t values =
      mmio_region_read32(i2c->params.base_addr, I2C_FIFO_STATUS_REG_OFFSET);
  if (fmt_fifo_level != NULL) {
    *fmt_fifo_level =
        bitfield_field32_read(values, I2C_FIFO_STATUS_FMTLVL_FIELD);
  }
  if (rx_fifo_level != NULL) {
    *rx_fifo_level = bitfield_field32_read(values, I2C_FIFO_STATUS_RXLVL_FIELD);
  }

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_read_byte(const dif_i2c_t *i2c, uint8_t *byte) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  uint32_t values =
      mmio_region_read32(i2c->params.base_addr, I2C_RDATA_REG_OFFSET);
  if (byte != NULL) {
    *byte = bitfield_field32_read(values, I2C_RDATA_RDATA_FIELD);
  }

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_write_byte_raw(const dif_i2c_t *i2c, uint8_t byte,
                                        dif_i2c_fmt_flags_t flags) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }
  // Validate that "write only" flags and "read only" flags are not set
  // simultaneously.
  bool has_write_flags = flags.start || flags.stop || flags.suppress_nak_irq;
  bool has_read_flags = flags.read || flags.read_cont;
  if (has_write_flags && has_read_flags) {
    return kDifI2cBadArg;
  }
  // Also, read_cont requires read.
  if (flags.read_cont && !flags.read) {
    return kDifI2cBadArg;
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
  mmio_region_write32(i2c->params.base_addr, I2C_FDATA_REG_OFFSET, fmt_byte);

  return kDifI2cOk;
}

dif_i2c_result_t dif_i2c_write_byte(const dif_i2c_t *i2c, uint8_t byte,
                                    dif_i2c_fmt_t code, bool suppress_nak_irq) {
  if (i2c == NULL) {
    return kDifI2cBadArg;
  }

  // Validate that `suppress_nak_irq` has not been mixed with an Rx code.
  if (suppress_nak_irq) {
    switch (code) {
      case kDifI2cFmtRx:
      case kDifI2cFmtRxContinue:
      case kDifI2cFmtRxStop:
        return kDifI2cBadArg;
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
      return kDifI2cBadArg;
  }

  return dif_i2c_write_byte_raw(i2c, byte, flags);
}
