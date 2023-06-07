// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/base/static_critical_version.h"

#include "sw/device/lib/base/macros.h"

/**
 * Static critical region format version.
 *
 * This value is placed at the start of RAM so that later boot stages have a
 * fixed place to look for this value for backward compatibility. It will be
 * populated by the ROM before the jump to ROM_EXT.
 */
OT_SET_BSS_SECTION(".static_critical.version",
                   uint32_t static_critical_version;)
