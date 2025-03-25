// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/rescue/sfdp.h"

#include "sw/device/silicon_creator/lib/drivers/spi_device.h"
#include "sw/device/silicon_creator/lib/drivers/spi_device_bfpt.h"

enum {
  /**
   * Rescue Flash size in bits.  The rescue implementation exposes
   * 4K of address space: 2K for data transfers and 1K of mailbox (plus
   * another 1K to be a power of 2).
   */
  kFlashBitCount = 1u << (kRescueDensity + 3),
  /**
   * 32-bit SFDP signature that indicates the presence of a SFDP table
   * (JESD216A 6.2.1).
   */
  kSfdpSignature = 0x50444653,
  /**
   * Number of parameter headers in the SFDP data structure (JESD216A 6.2.2).
   *
   * This number is zero-based. The SPI-DFU implementation has 2 parameter
   * headers: one for the Basic Flash Parameters Table (BFPT) and one for
   * the proprietary SDFU extension table.
   */
  kSfdpParamCount = 1,
  /**
   * SFDP major revision number (JESD216A 6.2.2).
   */
  kSfdpMajorRevision = 0x01,
  /**
   * SFDP minor revision number (JESD216A 6.2.2).
   */
  kSfdpMinorRevision = 0x05,
  /**
   * Unused value of header word 2 [31:24] (JESD216A 6.2.3).
   */
  kSfdpUnused = 0xff,
  /**
   * BFPT major revision number (JESD216A 6.4.1).
   */
  kBfptMajorRevision = 0x01,
  /**
   * BFPT minor revision number (JESD216A 6.4.1).
   */
  kBfptMinorRevision = 0x00,
  /**
   * LSB of BFPT's parameter ID (JESD216A 6.4.1).
   */
  kBfptParamIdLsb = 0x00,
  /**
   * MSB of BFPT's parameter ID (JESD216A 6.4.2).
   */
  kBfptParamIdMsb = 0xff,
  /**
   * Offset of the Basic Flash Parameter Table (BFPT) in the SFDP table.
   */
  kBfptTablePointer = offsetof(spi_device_sfdp_table_t, bfpt),
  /**
   * Value used for BFPT fields that are not supported.
   *
   * Note: A handful of BFPT fields, e.g. Msb of the 14th word of BFPT, use 1
   * instead. Such fields should be defined according to JESD216A instead of
   * using this value.
   */
  kBfptNotSupported = 0,
};

static_assert(kBfptTablePointer % sizeof(uint32_t) == 0,
              "BFPT must be word-aligned");

// Note: Words below are numbered starting from 1 to match JESD216A. Some fields
// that are not supported by OpenTitan are merged for the sake of conciseness.
// Unused/reserved fields that should be set to all 1s are ommitted due to the
// definition of `BFPT_FIELD_VALUE()` above. See JESD216A for more details.

// clang-format off
/**
 * BFPT 1st Word
 * -------------
 * [31:23]: Unused
 * [22:19]: (1S-1S-4S) (1S-4S-4S) (1S-2S-2S) DTR Clock (not supported: 0x0)
 * [18:17]: Address bytes (3-byte only addressing: 0)
 * [16:16]: (1S-1S-2S) (not supported: 0x0)
 * [15: 8]: 4 KiB erase instruction (0x20)
 * [ 7: 5]: Unused
 * [ 4: 4]: Write enable instruction (use 0x06 for WREN: 0x1)
 * [ 3: 3]: Volatile block protect bits (solely volatile: 0x1)
 * [ 2: 2]: Write granularity (buffer >= 64 B: 0x1)
 * [ 1: 0]: Block/sector erase sizes (uniform 4 KiB erase: 0x1)
 */
#define BFPT_WORD_1(X) \
  X(22, 19, kBfptNotSupported) & \
  X(18, 17, 0x0) & \
  X(16, 16, kBfptNotSupported) & \
  X(15,  8, kSpiDeviceOpcodeSectorErase) & \
  X( 4,  4, 0x1) & \
  X( 3,  3, 0x1) & \
  X( 2,  2, 0x1) & \
  X( 1,  0, 0x1)

/**
 * BFPT 2nd Word
 * -------------
 * [31:31]: Density greater than 2 Gib (0x0)
 * [30: 0]: Flash memory density in bits, zero-based.
 */
#define BFPT_WORD_2(X) \
  X(31, 31, 0) & \
  X(30,  0, kFlashBitCount - 1)

/**
 * BFPT 3rd Word
 * -------------
 * [31: 0]: Fast read (1S-4S-4S) (1S-1S-4S) (not supported, 0x0)
 */
#define BFPT_WORD_3(X) \
  X(31,  0, kBfptNotSupported)

/**
 * BFPT 4th Word
 * -------------
 * [31: 0]: Fast read (1S-1S-2S) (1S-2S-2S) (not supported, 0x0)
 */
#define BFPT_WORD_4(X) \
  X(31,  0, kBfptNotSupported)

/**
 * BFPT 5th Word
 * -------------
 * [31: 5]: Reserved
 * [ 4: 4]: Fast read (4S-4S-4S) support (not supported, 0x0)
 * [ 3: 1]: Reserved
 * [ 0: 0]: Fast read (2S-2S-2S) support (not supported, 0x0)
 */
#define BFPT_WORD_5(X) \
  X( 4,  4, kBfptNotSupported) & \
  X( 0,  0, kBfptNotSupported)

/**
 * BFPT 6th Word
 * -------------
 * [31:16]: Fast read (2S-2S-2S) (not supported, 0x0)
 * [15: 0]: Reserved
 */
#define BFPT_WORD_6(X) \
  X(31, 16, kBfptNotSupported)

/**
 * BFPT 7th Word
 * -------------
 * [31:16]: Fast read (4S-4S-4S) (not supported, 0x0)
 * [15: 0]: Reserved
 */
#define BFPT_WORD_7(X) \
  X(31, 16, kBfptNotSupported)

/**
 * BFPT 8th Word
 * -------------
 * [31:16]: Erase type 2 instruction and size (not supported, 0x0)
 * [15: 8]: Erase type 1 instruction (0x20)
 * [ 7: 0]: Erase type 1 size (4 KiB, 2^N bytes, N = 0x0c)
 */
#define BFPT_WORD_8(X) \
  X(31, 16, kBfptNotSupported) & \
  X(15,  8, kSpiDeviceOpcodeSectorErase) & \
  X( 7,  0, 0x0c)

/**
 * BFPT 9th Word
 * -------------
 * [31: 0]: Erase type 4 and 3 (not supported, 0x0)
 */
#define BFPT_WORD_9(X) \
  X(31,  0, kBfptNotSupported)
// clang-format on

const rescue_sfdp_table_t kRescueSfdpTable = {
    .header =
        {
            .signature = kSfdpSignature,
            .minor_revision = kSfdpMinorRevision,
            .major_revision = kSfdpMajorRevision,
            .param_count = kSfdpParamCount,
            .access_protocol = kSfdpUnused,
        },
    .phdr =
        {
            {
                .param_id_lsb = kBfptParamIdLsb,
                .minor_revision = kBfptMinorRevision,
                .major_revision = kBfptMajorRevision,
                .table_word_count = kRescueBfptSizeInWords,
                .table_pointer = {offsetof(rescue_sfdp_table_t, bfpt)},
                .param_id_msb = kBfptParamIdMsb,
            },
            {
                .param_id_lsb = 0xEF,  // lowRISC
                .minor_revision = 0,
                .major_revision = 1,
                .table_word_count = sizeof(sdfu_table_t) / sizeof(uint32_t),
                .table_pointer = {offsetof(rescue_sfdp_table_t, sdfu)},
                .param_id_msb =
                    12,  // page_number-1; The lowRISC JEDEC ID is on page 13.
            },
        },
    .bfpt =
        {
            BFPT_WORD_1(BFPT_FIELD_VALUE),
            BFPT_WORD_2(BFPT_FIELD_VALUE),
            BFPT_WORD_3(BFPT_FIELD_VALUE),
            BFPT_WORD_4(BFPT_FIELD_VALUE),
            BFPT_WORD_5(BFPT_FIELD_VALUE),
            BFPT_WORD_6(BFPT_FIELD_VALUE),
            BFPT_WORD_7(BFPT_FIELD_VALUE),
            BFPT_WORD_8(BFPT_FIELD_VALUE),
            BFPT_WORD_9(BFPT_FIELD_VALUE),
        },
    .sdfu =
        {
            .tag = kRescueSDFU,
            .length = sizeof(sdfu_table_t),
            .major = 1,
            .minor = 0,
            .mailbox_address = 0x800,
            .mailbox_size = 0x400,
            .dfu_size = 0x800,
        },
};
