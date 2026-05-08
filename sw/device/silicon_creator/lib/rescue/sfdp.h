// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_RESCUE_SFDP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_RESCUE_SFDP_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/spi_device.h"

#ifdef __cplusplus
extern "C" {
#endif

enum {
  /**
   * Rescue flash density: log2(4K bytes).  The rescue implementation exposes
   * 4K of address space: 2K for data transfers and 1K of mailbox (plus another
   * 1K to be a power of 2).
   */
  kRescueDensity = 12,
  /**
   * Size of rescue's BFPT in words.
   */
  kRescueBfptSizeInWords = 9,
  /**
   * The SDFU tag: ASCII `SDFU`.
   */
  kRescueSDFU = 0x55464453,
};

/**
 * The SDFU extension describes SPI-DFU in the SFDP table.
 */
typedef struct sdfu_table {
  /** tag: `SDFU`. */
  uint32_t tag;
  /** length: 16 bytes. */
  uint16_t length;
  /** Major version. */
  uint8_t major;
  /** Minor version. */
  uint8_t minor;
  /** The SDFU mailbox address. */
  uint32_t mailbox_address;
  /** The SDFU mailbox size. */
  uint16_t mailbox_size;
  /** The DFU transfer size. */
  uint16_t dfu_size;
} sdfu_table_t;
OT_ASSERT_MEMBER_OFFSET(sdfu_table_t, tag, 0);
OT_ASSERT_MEMBER_OFFSET(sdfu_table_t, length, 4);
OT_ASSERT_MEMBER_OFFSET(sdfu_table_t, major, 6);
OT_ASSERT_MEMBER_OFFSET(sdfu_table_t, minor, 7);
OT_ASSERT_MEMBER_OFFSET(sdfu_table_t, mailbox_address, 8);
OT_ASSERT_MEMBER_OFFSET(sdfu_table_t, mailbox_size, 12);
OT_ASSERT_MEMBER_OFFSET(sdfu_table_t, dfu_size, 14);
OT_ASSERT_SIZE(sdfu_table_t, 16);

/**
 * The Rescue SFDP table describes the flash interface for rescue mode.
 */
typedef struct rescue_sfdp_table {
  spi_device_sfdp_header_t header;
  spi_device_param_header_t phdr[2];
  uint32_t bfpt[kRescueBfptSizeInWords];
  sdfu_table_t sdfu;
} rescue_sfdp_table_t;
OT_ASSERT_MEMBER_OFFSET(rescue_sfdp_table_t, header, 0);
OT_ASSERT_MEMBER_OFFSET(rescue_sfdp_table_t, phdr, 8);
OT_ASSERT_MEMBER_OFFSET(rescue_sfdp_table_t, bfpt, 24);
OT_ASSERT_MEMBER_OFFSET(rescue_sfdp_table_t, sdfu, 60);
OT_ASSERT_SIZE(rescue_sfdp_table_t, 76);

extern const rescue_sfdp_table_t kRescueSfdpTable;
#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_RESCUE_SFDP_H_
