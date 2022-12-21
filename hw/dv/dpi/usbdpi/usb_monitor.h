// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_DPI_USBDPI_USB_MONITOR_H_
#define OPENTITAN_HW_DV_DPI_USBDPI_USB_MONITOR_H_
#include <stdbool.h>

/**
 * USB monitor context
 */
typedef struct usb_monitor_ctx usb_monitor_ctx_t;

/**
 * Create and initialise a USB monitor instance
 */
usb_monitor_ctx_t *usb_monitor_init(const char *filename);

/**
 * Finalise a USB monitor
 */
void usb_monitor_fin(usb_monitor_ctx_t *mon);

/**
 * Append a formatted message to the USB monitor log file
 */
void usb_monitor_log(usb_monitor_ctx_t *mon, const char *fmt, ...);

/**
 * Per-cycle monitoring of the USB
 */
void usb_monitor(usb_monitor_ctx_t *mon, int log, int tick, bool hdrive,
                 uint32_t p2d, uint32_t d2p, uint8_t *lastpid);

/**
 * Export diagnostic state for waveform viewing
 */
uint32_t usb_monitor_diags(usb_monitor_ctx_t *mon);

// TODO - temporary hook; tidy and ratify
const uint8_t *usb_monitor_get_data(usb_monitor_ctx_t *mon, size_t *plen);

#endif  // OPENTITAN_HW_DV_DPI_USBDPI_USB_MONITOR_H_
