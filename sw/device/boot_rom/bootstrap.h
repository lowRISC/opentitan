// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_BOOT_ROM_BOOTSTRAP_H_
#define OPENTITAN_SW_DEVICE_BOOT_ROM_BOOTSTRAP_H_

/**
 * A bootstrap error representing a flash erase failure.
 */
#define E_BS_ERASE 10
/**
 * A bootstrap error representing unexpectedly empty flash.
 */
#define E_BS_NOTEMPTY 11
/**
 * A bootstrap error representing a flash write error.
 */
#define E_BS_WRITE 12

/**
 * Bootstrap Flash with payload received on SPI device.
 *
 * The payload is expected to be split into frames as defined in
 * bootstrap_msgs.h. Frames are processed in consecutive number, with
 * `frame_num` in frame_hdr_t expected to increase monotonically.
 *
 * The last frame must be ord with FRAME_EOF_MARKER to signal the end of
 * payload transmission.
 *
 * @return Bootstrap status code.
 */
int bootstrap(void);

#endif  // OPENTITAN_SW_DEVICE_BOOT_ROM_BOOTSTRAP_H_
