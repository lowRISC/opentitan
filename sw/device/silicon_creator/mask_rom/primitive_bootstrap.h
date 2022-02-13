// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_PRIMITIVE_BOOTSTRAP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_PRIMITIVE_BOOTSTRAP_H_

#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"

/**
 * Bootstraps flash with payload received on SPI device.
 *
 * The payload is expected to be split into frames as defined in
 * bootstrap_msgs.h. Frames are processed in consecutive number, with
 * `frame_num` in `frame_hdr_t` expected to increase monotonically.
 *
 * The last frame must be ord with `FRAME_EOF_MARKER` to signal the end of
 * payload transmission.
 *
 * @param lc_state Lifecycle state.
 * @return Bootstrap status code.
 */
rom_error_t primitive_bootstrap(lifecycle_state_t lc_state);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_PRIMITIVE_BOOTSTRAP_H_
