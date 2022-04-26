// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_ROM_BOOTSTRAP_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_ROM_BOOTSTRAP_H_

#include "sw/device/lib/dif/dif_flash_ctrl.h"

typedef enum bootstrap_status {
  /**
   * Indicates success.
   */
  kBootstrapStatusOk = 0,
  /**
   * Indicates that erasing flash failed.
   */
  kBootstrapStatusEraseFailed = 10,
  /**
   * Indixcates an unexpectedly empty flash.
   */
  kBootstrapStatusNonemptyFlash = 11,
  /**
   * Indiccates that writing to flash failed.
   */
  kBootstrapStatusWriteFailed = 12,
} bootstrap_status_t;

/**
 * Bootstrap flash with payload received on SPI device.
 *
 * The payload is expected to be split into frames as defined in
 * spiflash_frame.h. Frames are processed in consecutive number, with
 * `frame_num` in `spiflash_frame_header_t` expected to increase
 * monotonically.
 *
 * The last frame number must be or'ed with SPIFLASH_FRAME_EOF_MARKER to
 * signal the end of payload transmission.
 *
 * @param flash_ctrl A handle to a flash_ctrl.
 * @return Bootstrap status code.
 */
bootstrap_status_t bootstrap(dif_flash_ctrl_state_t *flash_ctrl);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_ROM_BOOTSTRAP_H_
