// Copyright lowRISC contributors (OpenTitan project).
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

static void spin_while_status_bit(const dif_i2c_t *i2c, uint32_t bit,
                                  bool set) {
  uint32_t reg = 0;
  do {
    reg = mmio_region_read32(i2c->base_addr, I2C_STATUS_REG_OFFSET);
  } while (bitfield_bit32_read(reg, bit) == set);
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
  status->ack_control_en = bitfield_bit32_read(reg, I2C_CTRL_ACK_CTRL_EN_BIT);
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
  status->ack_ctrl_stretch =
      bitfield_bit32_read(reg, I2C_STATUS_ACK_CTRL_STRETCH_BIT);

  return kDifOk;
}

dif_result_t dif_i2c_get_controller_halt_events(
    const dif_i2c_t *i2c, dif_i2c_controller_halt_events_t *events) {
  if (i2c == NULL || events == NULL) {
    return kDifBadArg;
  }
  uint32_t reg =
      mmio_region_read32(i2c->base_addr, I2C_CONTROLLER_EVENTS_REG_OFFSET);
  events->nack_received =
      bitfield_bit32_read(reg, I2C_CONTROLLER_EVENTS_NACK_BIT);
  events->unhandled_nack_timeout = bitfield_bit32_read(
      reg, I2C_CONTROLLER_EVENTS_UNHANDLED_NACK_TIMEOUT_BIT);
  events->bus_timeout =
      bitfield_bit32_read(reg, I2C_CONTROLLER_EVENTS_BUS_TIMEOUT_BIT);
  events->arbitration_lost =
      bitfield_bit32_read(reg, I2C_CONTROLLER_EVENTS_ARBITRATION_LOST_BIT);
  return kDifOk;
}

dif_result_t dif_i2c_clear_controller_halt_events(
    const dif_i2c_t *i2c, dif_i2c_controller_halt_events_t events) {
  if (i2c == NULL) {
    return kDifBadArg;
  }
  uint32_t reg = 0;
  reg = bitfield_bit32_write(reg, I2C_CONTROLLER_EVENTS_NACK_BIT,
                             events.nack_received);
  reg = bitfield_bit32_write(reg,
                             I2C_CONTROLLER_EVENTS_UNHANDLED_NACK_TIMEOUT_BIT,
                             events.unhandled_nack_timeout);
  reg = bitfield_bit32_write(reg, I2C_CONTROLLER_EVENTS_BUS_TIMEOUT_BIT,
                             events.bus_timeout);
  reg = bitfield_bit32_write(reg, I2C_CONTROLLER_EVENTS_ARBITRATION_LOST_BIT,
                             events.arbitration_lost);
  mmio_region_write32(i2c->base_addr, I2C_CONTROLLER_EVENTS_REG_OFFSET, reg);
  return kDifOk;
}

dif_result_t dif_i2c_get_target_tx_halt_events(
    const dif_i2c_t *i2c, dif_i2c_target_tx_halt_events_t *events) {
  if (i2c == NULL || events == NULL) {
    return kDifBadArg;
  }
  uint32_t reg =
      mmio_region_read32(i2c->base_addr, I2C_TARGET_EVENTS_REG_OFFSET);
  events->tx_pending =
      bitfield_bit32_read(reg, I2C_TARGET_EVENTS_TX_PENDING_BIT);
  events->bus_timeout =
      bitfield_bit32_read(reg, I2C_TARGET_EVENTS_BUS_TIMEOUT_BIT);
  events->arbitration_lost =
      bitfield_bit32_read(reg, I2C_TARGET_EVENTS_ARBITRATION_LOST_BIT);
  return kDifOk;
}

dif_result_t dif_i2c_clear_target_tx_halt_events(
    const dif_i2c_t *i2c, dif_i2c_target_tx_halt_events_t events) {
  if (i2c == NULL) {
    return kDifBadArg;
  }
  uint32_t reg = 0;
  reg = bitfield_bit32_write(reg, I2C_TARGET_EVENTS_TX_PENDING_BIT,
                             events.tx_pending);
  reg = bitfield_bit32_write(reg, I2C_TARGET_EVENTS_BUS_TIMEOUT_BIT,
                             events.bus_timeout);
  reg = bitfield_bit32_write(reg, I2C_TARGET_EVENTS_ARBITRATION_LOST_BIT,
                             events.arbitration_lost);
  mmio_region_write32(i2c->base_addr, I2C_TARGET_EVENTS_REG_OFFSET, reg);
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

  // For clock stretching detection to work, the SCL high and low time must be
  // at least 4 cycles.
  if (config->scl_time_high_cycles < kDifI2cInputDelayCycles) {
    config->scl_time_high_cycles = kDifI2cInputDelayCycles;
  }
  if (config->scl_time_low_cycles < kDifI2cInputDelayCycles) {
    config->scl_time_low_cycles = kDifI2cInputDelayCycles;
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

dif_result_t dif_i2c_set_host_watermarks(const dif_i2c_t *i2c,
                                         dif_i2c_level_t rx_level,
                                         dif_i2c_level_t fmt_level) {
  // Check that the FIFO levels are sensible; setting RX level equal to the
  // depth deactivates its interrupt, but setting FMT level to that would result
  // in continual interrupt assertion.
  if (i2c == NULL || rx_level > I2C_PARAM_FIFO_DEPTH ||
      fmt_level >= I2C_PARAM_FIFO_DEPTH) {
    return kDifBadArg;
  }

  uint32_t ctrl_value =
      mmio_region_read32(i2c->base_addr, I2C_HOST_FIFO_CONFIG_REG_OFFSET);
  ctrl_value = bitfield_field32_write(
      ctrl_value, I2C_HOST_FIFO_CONFIG_RX_THRESH_FIELD, rx_level);
  ctrl_value = bitfield_field32_write(
      ctrl_value, I2C_HOST_FIFO_CONFIG_FMT_THRESH_FIELD, fmt_level);
  mmio_region_write32(i2c->base_addr, I2C_HOST_FIFO_CONFIG_REG_OFFSET,
                      ctrl_value);

  return kDifOk;
}

dif_result_t dif_i2c_set_target_watermarks(const dif_i2c_t *i2c,
                                           dif_i2c_level_t tx_level,
                                           dif_i2c_level_t acq_level) {
  // Check that the FIFO levels are sensible; setting ACQ level equal to the
  // depth deactivates its interrupt, but setting TX level to that would result
  // in continual interrupt assertion.
  if (i2c == NULL || acq_level > I2C_PARAM_ACQ_FIFO_DEPTH ||
      tx_level >= I2C_PARAM_FIFO_DEPTH) {
    return kDifBadArg;
  }

  uint32_t ctrl_value =
      mmio_region_read32(i2c->base_addr, I2C_TARGET_FIFO_CONFIG_REG_OFFSET);
  ctrl_value = bitfield_field32_write(
      ctrl_value, I2C_TARGET_FIFO_CONFIG_TX_THRESH_FIELD, tx_level);
  ctrl_value = bitfield_field32_write(
      ctrl_value, I2C_TARGET_FIFO_CONFIG_ACQ_THRESH_FIELD, acq_level);
  mmio_region_write32(i2c->base_addr, I2C_TARGET_FIFO_CONFIG_REG_OFFSET,
                      ctrl_value);

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

dif_result_t dif_i2c_addr_nack_set_enabled(const dif_i2c_t *i2c,
                                           dif_toggle_t state) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  if (!dif_is_valid_toggle(state)) {
    return kDifBadArg;
  }
  bool flag = dif_toggle_to_bool(state);

  uint32_t reg = mmio_region_read32(i2c->base_addr, I2C_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, I2C_CTRL_NACK_ADDR_AFTER_TIMEOUT_BIT, flag);
  mmio_region_write32(i2c->base_addr, I2C_CTRL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_i2c_ack_ctrl_set_enabled(const dif_i2c_t *i2c,
                                          dif_toggle_t state) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  if (!dif_is_valid_toggle(state)) {
    return kDifBadArg;
  }
  bool flag = dif_toggle_to_bool(state);

  uint32_t reg = mmio_region_read32(i2c->base_addr, I2C_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, I2C_CTRL_ACK_CTRL_EN_BIT, flag);
  mmio_region_write32(i2c->base_addr, I2C_CTRL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_i2c_multi_controller_monitor_set_enabled(const dif_i2c_t *i2c,
                                                          dif_toggle_t state) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  if (!dif_is_valid_toggle(state)) {
    return kDifBadArg;
  }
  bool flag = dif_toggle_to_bool(state);

  uint32_t reg = mmio_region_read32(i2c->base_addr, I2C_CTRL_REG_OFFSET);
  reg =
      bitfield_bit32_write(reg, I2C_CTRL_MULTI_CONTROLLER_MONITOR_EN_BIT, flag);
  mmio_region_write32(i2c->base_addr, I2C_CTRL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_i2c_target_tx_stretch_ctrl_set_enabled(const dif_i2c_t *i2c,
                                                        dif_toggle_t state) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  if (!dif_is_valid_toggle(state)) {
    return kDifBadArg;
  }
  bool flag = dif_toggle_to_bool(state);

  uint32_t reg = mmio_region_read32(i2c->base_addr, I2C_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, I2C_CTRL_TX_STRETCH_CTRL_EN_BIT, flag);
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
                                     dif_i2c_level_t *fmt_fifo_level,
                                     dif_i2c_level_t *rx_fifo_level,
                                     dif_i2c_level_t *tx_fifo_level,
                                     dif_i2c_level_t *acq_fifo_level) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  // Host-side FIFO levels
  uint32_t values =
      mmio_region_read32(i2c->base_addr, I2C_HOST_FIFO_STATUS_REG_OFFSET);
  if (fmt_fifo_level != NULL) {
    *fmt_fifo_level = (dif_i2c_level_t)bitfield_field32_read(
        values, I2C_HOST_FIFO_STATUS_FMTLVL_FIELD);
  }
  if (rx_fifo_level != NULL) {
    *rx_fifo_level = (dif_i2c_level_t)bitfield_field32_read(
        values, I2C_HOST_FIFO_STATUS_RXLVL_FIELD);
  }

  // Target-side FIFO levels
  values =
      mmio_region_read32(i2c->base_addr, I2C_TARGET_FIFO_STATUS_REG_OFFSET);
  if (tx_fifo_level != NULL) {
    *tx_fifo_level = (dif_i2c_level_t)bitfield_field32_read(
        values, I2C_TARGET_FIFO_STATUS_TXLVL_FIELD);
  }
  if (acq_fifo_level != NULL) {
    *acq_fifo_level = (dif_i2c_level_t)bitfield_field32_read(
        values, I2C_TARGET_FIFO_STATUS_ACQLVL_FIELD);
  }

  return kDifOk;
}

dif_result_t dif_i2c_get_auto_ack_count(const dif_i2c_t *i2c, uint16_t *count) {
  if (i2c == NULL || count == NULL) {
    return kDifBadArg;
  }

  uint32_t reg =
      mmio_region_read32(i2c->base_addr, I2C_TARGET_ACK_CTRL_REG_OFFSET);
  *count =
      (uint16_t)bitfield_field32_read(reg, I2C_TARGET_ACK_CTRL_NBYTES_FIELD);

  return kDifOk;
}

dif_result_t dif_i2c_set_auto_ack_count(const dif_i2c_t *i2c, uint16_t count) {
  if (i2c == NULL) {
    return kDifBadArg;
  }
  if (count > I2C_TARGET_ACK_CTRL_NBYTES_MASK) {
    return kDifBadArg;
  }

  uint32_t reg =
      bitfield_field32_write(0, I2C_TARGET_ACK_CTRL_NBYTES_FIELD, count);
  mmio_region_write32(i2c->base_addr, I2C_TARGET_ACK_CTRL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_i2c_nack_transaction(const dif_i2c_t *i2c) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, I2C_TARGET_ACK_CTRL_NACK_BIT, true);
  mmio_region_write32(i2c->base_addr, I2C_TARGET_ACK_CTRL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_i2c_get_pending_acq_byte(const dif_i2c_t *i2c, uint8_t *data) {
  if (i2c == NULL || data == NULL) {
    return kDifBadArg;
  }

  *data = 0xffu &
          mmio_region_read32(i2c->base_addr, I2C_ACQ_FIFO_NEXT_DATA_REG_OFFSET);

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

dif_result_t dif_i2c_read_bytes(const dif_i2c_t *i2c, size_t size,
                                uint8_t *buffer) {
  if (i2c == NULL || buffer == NULL) {
    return kDifBadArg;
  }

  while (size--) {
    spin_while_status_bit(i2c, I2C_STATUS_RXEMPTY_BIT, /*set*/ true);
    uint32_t values = mmio_region_read32(i2c->base_addr, I2C_RDATA_REG_OFFSET);
    *(buffer++) = (uint8_t)bitfield_field32_read(values, I2C_RDATA_RDATA_FIELD);
  }

  return kDifOk;
}

static inline dif_result_t parse_flags(dif_i2c_fmt_flags_t flags,
                                       uint32_t *fmt_byte) {
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

  *fmt_byte = bitfield_bit32_write(*fmt_byte, 8, flags.start);
  *fmt_byte = bitfield_bit32_write(*fmt_byte, I2C_FDATA_STOP_BIT, flags.stop);
  *fmt_byte = bitfield_bit32_write(*fmt_byte, I2C_FDATA_READB_BIT, flags.read);
  *fmt_byte =
      bitfield_bit32_write(*fmt_byte, I2C_FDATA_RCONT_BIT, flags.read_cont);
  *fmt_byte = bitfield_bit32_write(*fmt_byte, I2C_FDATA_NAKOK_BIT,
                                   flags.suppress_nak_irq);

  return kDifOk;
}
dif_result_t dif_i2c_write_bytes_raw(const dif_i2c_t *i2c, size_t size,
                                     const uint8_t *bytes,
                                     dif_i2c_fmt_flags_t flags) {
  if (i2c == NULL || bytes == NULL || size == 0) {
    return kDifBadArg;
  }
  uint32_t fmt_byte = 0;
  DIF_RETURN_IF_ERROR(parse_flags(flags, &fmt_byte));

  for (size_t i = 0; i < size; ++i) {
    uint32_t reg =
        bitfield_field32_write(fmt_byte, I2C_FDATA_FBYTE_FIELD, bytes[i]);
    mmio_region_write32(i2c->base_addr, I2C_FDATA_REG_OFFSET, reg);
    spin_while_status_bit(i2c, I2C_STATUS_FMTFULL_BIT, /*set*/ true);
  }

  return kDifOk;
}

dif_result_t dif_i2c_write_byte_raw(const dif_i2c_t *i2c, uint8_t byte,
                                    dif_i2c_fmt_flags_t flags) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  uint32_t fmt_byte = 0;
  DIF_RETURN_IF_ERROR(parse_flags(flags, &fmt_byte));
  fmt_byte = bitfield_field32_write(fmt_byte, I2C_FDATA_FBYTE_FIELD, byte);
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

dif_result_t dif_i2c_enable_clock_timeout(const dif_i2c_t *i2c,
                                          dif_i2c_scl_timeout_t timeout_type,
                                          uint32_t cycles) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  bool timeout_en = false;
  uint8_t timeout_mode = 0;
  switch (timeout_type) {
    case kDifI2cSclTimeoutDisabled:
      timeout_en = false;
      break;
    case kDifI2cSclTimeoutStretch:
      timeout_en = true;
      timeout_mode = I2C_TIMEOUT_CTRL_MODE_VALUE_STRETCH_TIMEOUT;
      break;
    case kDifI2cSclTimeoutBus:
      timeout_en = true;
      timeout_mode = I2C_TIMEOUT_CTRL_MODE_VALUE_BUS_TIMEOUT;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t config = 0;
  config = bitfield_bit32_write(config, I2C_TIMEOUT_CTRL_EN_BIT, timeout_en);
  config =
      bitfield_bit32_write(config, I2C_TIMEOUT_CTRL_MODE_BIT, timeout_mode);
  config = bitfield_field32_write(config, I2C_TIMEOUT_CTRL_VAL_FIELD, cycles);
  mmio_region_write32(i2c->base_addr, I2C_TIMEOUT_CTRL_REG_OFFSET, config);
  return kDifOk;
}

dif_result_t dif_i2c_set_device_id(const dif_i2c_t *i2c,
                                   const dif_i2c_id_t *id0,
                                   const dif_i2c_id_t *id1) {
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
