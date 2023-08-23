// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_STATIC_CRITICAL_VERSION_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_STATIC_CRITICAL_VERSION_H_

#include <stdint.h>

enum {
  /**
   * Static critical region format version 1 value.
   */
  kStaticCriticalVersion1 = 0xb86fa4b0,
  /**
   * Static critical region format version 2 value.
   */
  kStaticCriticalVersion2 = 0x8d9fc439,
};

/**
 * Extern declaration for the static_critical region format version placed at
 * the start of RAM.
 */
extern uint32_t static_critical_version;

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_STATIC_CRITICAL_VERSION_H_
