// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_DPI_USBDPI_USB_MONITOR_H_
#define OPENTITAN_HW_DV_DPI_USBDPI_USB_MONITOR_H_
#include <stdbool.h>
#include <stdint.h>

/**
 * USB monitor context
 */
typedef struct usb_monitor_ctx usb_monitor_ctx_t;

// USB data callback types
typedef enum {
  UsbMon_DataType_Sync,
  UsbMon_DataType_PID,
  UsbMon_DataType_Byte,
  UsbMon_DataType_EOP
} usbmon_data_type_t;

/**
 * Callback function for USB data
 */
typedef void (*usb_monitor_data_callback_t)(void *ctx_v,
                                            usbmon_data_type_t type, uint8_t d);

/**
 * Create and initialize a USB monitor instance
 *
 * @param  filename  Filename to be used for log file
 * @param  data_cb   USB data callback function
 * @param  data_ctx  Context for data callback
 * @return           USB monitor context
 */
usb_monitor_ctx_t *usb_monitor_init(const char *filename,
                                    usb_monitor_data_callback_t data_cb,
                                    void *data_ctx);

/**
 * Finalize a USB monitor
 *
 * @param mon        USB monitor context
 */
void usb_monitor_fin(usb_monitor_ctx_t *mon);

/**
 * Append a formatted message to the USB monitor log file
 *
 * @param mon        USB monitor context
 * @param fmt        Format specifier for message
 */
void usb_monitor_log(usb_monitor_ctx_t *mon, const char *fmt, ...);

/**
 * Per-cycle monitoring of the USB
 *
 * @param mon        USB monitor context
 * @param loglevel   Level of logging information required
 * @param tick_bits  Elapsed simulation time in USB bit intervals (12Mbps)
 * @param hdrive     Indicates whether the host is driving the bus
 * @param d2p        Signals from USBDEV to DPI model
 * @param p2d        Signals from DPI model to USBDEV
 * @param lastpid    Receives the most-recently decoded PID (either direction)
 */
void usb_monitor(usb_monitor_ctx_t *mon, int log, uint32_t tick_bits,
                 bool hdrive, uint32_t p2d, uint32_t d2p, uint8_t *lastpid);

/**
 * Export diagnostic state for waveform viewing
 *
 * @param mon        USB monitor context
 * @return           Diagnostic state information (see usbdpi.sv)
 */
uint32_t usb_monitor_diags(usb_monitor_ctx_t *mon);

#endif  // OPENTITAN_HW_DV_DPI_USBDPI_USB_MONITOR_H_
