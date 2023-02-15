// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_STREAM_TEST_H_
#define OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_STREAM_TEST_H_
#include <cstdint>

#ifndef ABS
#define ABS(x) (((x) < 0) ? -(x) : (x))
#endif

// Maximum number of concurrent streams
#ifdef USBDEV_NUM_ENDPOINTS
#define STREAMS_MAX (USBDEV_NUM_ENDPOINTS - 1U)
#else
#define STREAMS_MAX 11U
#endif

/**
 * Simple container for test configuration
 */
struct TestConfig {
  /**
   * Initialize test settings
   */
  TestConfig(bool init_verb, bool init_retr, bool init_chk, bool init_send)
      : verbose(init_verb),
        retrieve(init_retr),
        check(init_chk),
        send(init_send) {}
  /**
   * Verbose logging/diagnostic reporting
   */
  bool verbose;
  /**
   * Retrieve data from the device
   */
  bool retrieve;
  /**
   * Check the retrieved data against expectations
   */
  bool check;
  /**
   * Send data to the device
   */
  bool send;
};

// Has any data yet been received from the device?
extern bool received;

// Time of first data reception
extern uint64_t start_time;

// Configuration settings for the test
extern TestConfig cfg;

/**
 * Report command line syntax
 */
void report_syntax(void);

#endif  // OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_STREAM_TEST_H_
