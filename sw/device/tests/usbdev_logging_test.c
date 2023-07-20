// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB logging test
//
// This test exercises the USB logging functionality. It first initializes
// 4 logging streams via the USB device and cable to the host, and then
// transmits a number of tests messages to each stream directly.
//
// Subsequently, it reinitializes the software layer with redirection of
// stdout via a single stream and performs, to check that the LOG_INFO()
// and base_printf() functionality works over the USB connection.
//
// Currently this test requires manual support on the host side; on a Linux-
// based host, running 4 processes as follows will allow the test to complete:
//
//  cat /dev/ttyUSB0
//  cat /dev/ttyUSB1
//  cat /dev/ttyUSB2
//  cat /dev/ttyUSB3
//
// Note that the assigned port numbers on the host may differ from the defaults
// shown above. Since the logging streams have been initialized for reliable
// transfer, the CPU/test will stall until the receiving processes on the host
// have collected all of the logging output.

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/usb_logging.h"

// Presently we must reinstate the UART output manually.
#include "sw/device/lib/dif/dif_uart.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

/**
 * Number of concurrent logging streams to test.
 */
static const unsigned kNumStreams = 4u;
/**
 * Number of iterations of logging message.
 */
static const unsigned kNumIters = 1000u;

// Because this test redirects the console output to the USB, we need to
// indicate to OTTF that the console must be reinitialized before test
// completion can be reported.
OTTF_DEFINE_TEST_CONFIG(.console.test_may_clobber = true);

bool test_main(void) {
  LOG_INFO("Running USBDEV_LOGGING test");

  // ----------------- Test the more generic, direct interface ----------------

  // Enable USB logging
  CHECK_STATUS_OK(
      usb_logging_init(NULL, 0u, kNumStreams, (1u << kNumStreams) - 1u, true));

  for (uint8_t s = 0u; s < kNumStreams; ++s) {
    usb_logging_text(s, "USB - Logging via direct interface\n");
  }

  for (unsigned iter = 0u; iter < kNumIters; ++iter) {
    for (uint8_t s = 0u; s < kNumStreams; ++s) {
      char buf[44];
      size_t len = base_snprintf(buf, sizeof(buf),
                                 "S%u: Now logging %u over USB\n", s, iter);
      CHECK_STATUS_OK(usb_logging_data(s, (uint8_t *)buf, len));
    }
  }

  // Finalize the logging code.
  CHECK_STATUS_OK(usb_logging_fin(true, false));

  // ------------------- Test redirection of stdout via OTTF ------------------

  // Enable logging of stdout traffic over USB
  CHECK_STATUS_OK(usb_logging_enable());

  for (unsigned iter = 0u; iter < kNumIters; ++iter) {
    LOG_INFO("Now logging %u over USB", iter);
  }

  // Just a quantity of data as ASCII hex...
  const uint32_t kSramStart = TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR;
  const uint32_t kSramSize = TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES;
  base_hexdump((char *)kSramStart, kSramSize);

  CHECK_STATUS_OK(usb_logging_fin(true, true));

  return true;
}
