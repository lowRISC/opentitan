// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_STREAM_TEST_H_
#define OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_STREAM_TEST_H_
#include <cstdint>

// Maximum number of concurrent streams, leaving at least one endpoint for
// the Default Control Pipe.
#ifdef USBDEV_NUM_ENDPOINTS
#define STREAMS_MAX (USBDEV_NUM_ENDPOINTS - 1U)
#else
#define STREAMS_MAX 11U
#endif

/**
 * Simple container for test configuration.
 */
struct TestConfig {
  /**
   * Initialize test settings; see descriptions below.
   */
  TestConfig(bool init_verb, bool init_retr, bool init_chk, bool init_send)
      : verbose(init_verb),
        retrieve(init_retr),
        check(init_chk),
        send(init_send),
#if STREAMTEST_LIBUSB
        serial(false),
#else
        serial(true),
#endif
        suspending(false) {
  }
  /**
   * Verbose logging/diagnostic reporting.
   */
  bool verbose;
  /**
   * Override the stream flags using the command line arguments?
   */
  bool override_flags;
  /**
   * Retrieve data from the device.
   */
  bool retrieve;
  /**
   * Check the retrieved data against expectations.
   */
  bool check;
  /**
   * Send data to the device.
   */
  bool send;
  /**
   * Favor serial ports over libusb for Bulk Transfer streams?
   */
  bool serial;
  /**
   * Are we performing suspend-resume testing whilst streaming?
   */
  bool suspending;
};

// Has any data yet been received from the device?
extern bool received;

// Time of first data reception.
extern uint64_t start_time;

// Configuration settings for the test.
extern TestConfig cfg;

/**
 * Report command line syntax.
 */
void ReportSyntax(void);

#endif  // OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_STREAM_TEST_H_
