// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_USB_LOGGING_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_USB_LOGGING_H_
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/testing/usb_testutils.h"

// Maximum number of streams supported by logging over USB.
enum {
  kUSBLogMaxStreams = 4u,
};

/**
 * Initiate logging of stdout traffic over USB, using internal state
 * structure and a single stream, for minimal external code.
 *
 * @return The result of the operation.
 */

OT_WARN_UNUSED_RESULT
status_t usb_logging_enable(void);

/**
 * Generic initialization of logging streams via USB device; traffic delivery
 * for each stream may optionally be reliable, meaning that the calling code
 * will block if there is insufficient buffer space and/or the USB host has not
 * yet received earlier traffic.
 *
 * To integrate with other code that is using the USB testutils, specify the
 * context pointer for the usb_testutils layer, along with the number of the
 * first endpoint to used for logging.
 *
 * If logging is the only user of the USB device, simply pass NULL and ep_first
 * may be zero.
 *
 * @param  usbutils   Context for usb_testutils layer or NULL.
 * @param  nstreams   Number of logging streams.
 * @param  ep_first   First endpoint number to be used.
 * @param  mreliable  Bitmap of which logging streams shall provide reliable
 *                    delivery.
 * @param  remap      Is remapping of non-printable characters required?
 * @return The result of the operation.
 */

OT_WARN_UNUSED_RESULT
status_t usb_logging_init(usb_testutils_ctx_t *usbutils, uint8_t ep_first,
                          uint8_t nstreams, uint32_t reliable, bool remap);

/**
 * Send a log message via the given stream.
 *
 * @param  stream     Stream number.
 * @param  text       The text to be sent.
 * @return The result of the operation.
 */
// Use of result not required for unreliable logging traffic.
status_t usb_logging_text(uint8_t stream, const char *text);

/**
 * Send a sequence of bytes via the given stream.
 *
 * @param  stream     Stream number.
 * @param  data       Start of byte sequence.
 * @param  len        Number of bytes to be sent.
 * @return The result of the operation.
 */
// Use of result not required for unreliable logging traffic.
status_t usb_logging_data(uint8_t stream, const uint8_t *data, unsigned len);

/**
 * Ensure that all log data on this stream is flushed upstream to the host;
 * this should be employed only where absolutely necessary, to ensure visibility
 * of specific output.
 *
 * In normal usage, log data will be periodically flushed
 */
status_t usb_logging_flush(uint8_t stream);

/**
 * Finalize USB logging streams, optionally waiing until all buffered logging
 * data has been transmitted to the host.
 *
 * @param  wait       Whether to wait for all buffered data to be transmitted.
 * @param  disconnect Indicates whether to disconnect from the USB.
 * @return The result of the operation.
 */

OT_WARN_UNUSED_RESULT
status_t usb_logging_fin(bool wait, bool disconnect);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_USB_LOGGING_H_
