// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_H_

#include <stdbool.h>
#include <stdint.h>

typedef enum dt_device_type {
  kDtDeviceTypeUnknown = 0,
  kDtDeviceTypeAdcCtrl,
  kDtDeviceTypeAes,
  kDtDeviceTypeAlertHandler,
  kDtDeviceTypeAonTimer,
  kDtDeviceTypeAst,
  kDtDeviceTypeClkmgr,
  kDtDeviceTypeCsrng,
  kDtDeviceTypeEdn,
  kDtDeviceTypeEntropySrc,
  kDtDeviceTypeFlashCtrl,
  kDtDeviceTypeGpio,
  kDtDeviceTypeHmac,
  kDtDeviceTypeI2c,
  kDtDeviceTypeKeymgr,
  kDtDeviceTypeKmac,
  kDtDeviceTypeLcCtrl,
  kDtDeviceTypeOtbn,
  kDtDeviceTypeOtpCtrl,
  kDtDeviceTypePattgen,
  kDtDeviceTypePinmux,
  kDtDeviceTypePwm,
  kDtDeviceTypePwrmgr,
  kDtDeviceTypeRomCtrl,
  kDtDeviceTypeRstmgr,
  kDtDeviceTypeRvCoreIbex,
  kDtDeviceTypeRvDm,
  kDtDeviceTypeRvPlic,
  kDtDeviceTypeRvTimer,
  kDtDeviceTypeSensorCtrl,
  kDtDeviceTypeSpiDevice,
  kDtDeviceTypeSpiHost,
  kDtDeviceTypeSramCtrl,
  kDtDeviceTypeSysrstCtrl,
  kDtDeviceTypeUart,
  kDtDeviceTypeUsbdev,
  kDtDeviceTypeCount,
} dt_device_type_t;

// An ID representing a particular device, with 0 reserved for "unknown."
typedef uint32_t dt_device_t;

enum {
  kDtDeviceUnknown = 0,
  kDtClockUnknown = 0,
  kDtIrqUnknown = 0,
};

/**
 * Get the number of devices of the specified `dev_type`.
 *
 * The number returned indicates the maximum `dev_idx` available to
 * `dt_get_device`.
 */
extern uint32_t dt_num_devices(dt_device_type_t dev_type);

/**
 * Get the device ID corresponding to the n'th device of the provided type.
 */
extern dt_device_t dt_get_device(dt_device_type_t dev_type, uint16_t dev_idx);

/**
 * Get the device type for a given device.
 */
extern dt_device_type_t dt_device_get_type(dt_device_t dev);

/**
 * Get the base address of a device's specified register block.
 *
 * A value of 0 indicates no such block is mapped.
 */
extern uintptr_t dt_device_reg_addr(dt_device_t dev, uint32_t reg_block_idx);

/**
 * Get the IRQ ID corresponding to a device's given `irq_type`.
 *
 * The ID 0 indicates an invalid argument or unknown ID.
 */
extern uint32_t dt_device_irq_id(dt_device_t dev, uint32_t irq_type);

/**
 * Get the requesting device corresponding to the given global IRQ ID.
 */
extern dt_device_t dt_irq_to_device(uint32_t irq);

// An ID representing a clock, with 0 reserved for "unknown."
typedef uint32_t dt_clock_t;

/**
 * Returns the clock frequency of the specified clock in Hz.
 */
extern uint32_t dt_clock_frequency(dt_clock_t clk);

/**
 * Return the clock ID for clock connected to the given device's `clock_port`.
 */
extern dt_clock_t dt_device_clock_id(dt_device_t dev, uint32_t clock_port);

/**
 * Returns whether a given device is connected sufficiently to use externally.
 * For example, if the device corresponding to I2C0 is present in the chip but
 * not connected to an I2C bus on the board, this function would return false.
 *
 * TODO: This API may need to grow to accommodate specific device features. For
 * example, spi_device supports both a flash feature and a TPM feature, but it's
 * not clear from this one function whether both are available. Another example
 * for the same device would be ordinary SPI vs. QSPI. Perhaps pinctrl functions
 * should distinguish between "unavailable" and "connected to DIO".
 */
extern bool dt_device_pinctrl_is_ok(dt_device_t dev);

/**
 * The upper 15 bits are a mux ID, and the lower 16 are the selection value for
 * the indicated mux. Negative values signify "no entry".
 */
typedef int32_t dt_pinctrl_cfg_t;

/**
 * Construct a dt_pinctrl_cfg_t from its two components.
 */
#define dt_pinctrl_cfg_from_parts(mux_id, selection) \
  ((dt_pinctrl_cfg_t)((((uint32_t)mux_id & 0x7fffu) << 16) | selection))

/**
 * Return false if the given pinctrl configuration is empty and should be
 * discarded. Empty configuration values imply that the associated pin does not
 * require mux selection or is not connected.
 */
inline bool dt_pinctrl_cfg_is_empty(dt_pinctrl_cfg_t cfg) { return cfg < 0; }

/**
 * Extract the selection value for a mux from the provided pinctrl
 * configuration.
 */
inline uint16_t dt_pinctrl_selection_from_cfg(dt_pinctrl_cfg_t cfg) {
  return ((uint32_t)cfg & 0xffffu);
}

/**
 * Extract the mux ID from the provided pinctrl configuration.
 */
inline uint16_t dt_pinctrl_mux_from_cfg(dt_pinctrl_cfg_t cfg) {
  return (((uint32_t)cfg & 0x7fff0000u) >> 16);
}

/**
 * Get output pad mux configuration for a given device.
 */
extern dt_pinctrl_cfg_t dt_pinctrl_get_padmux_config(dt_device_t dev,
                                                     uint32_t idx);

/**
 * Get peripheral input mux configuration for a given device.
 */
extern dt_pinctrl_cfg_t dt_pinctrl_get_periphmux_config(dt_device_t dev,
                                                        uint32_t idx);

/**
 * For straps and initial UART configs
 */
extern uint32_t dt_pinctrl_boot_padmux_config_len(void);
extern uint32_t dt_pinctrl_boot_periphmux_config_len(void);
extern dt_pinctrl_cfg_t dt_pinctrl_get_boot_padmux_config(uint32_t idx);
extern dt_pinctrl_cfg_t dt_pinctrl_get_boot_periphmux_config(uint32_t idx);

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_H_
