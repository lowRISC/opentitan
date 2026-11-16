// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdalign.h>
#include <stddef.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/rom/fips_kat_table.h"

/**
 * =============================================================================
 * FIPS 140-3 Known Answer Test (KAT) Vectors in ROM
 * =============================================================================
 *
 * Placement & Footprint Architecture:
 * -----------------------------------
 * All 31 KAT descriptor entries and vector payloads are grouped into a single
 * combined struct (`kFipsKatRomBlob`) placed in `.fips_kat` and anchored by
 * `rom.ld` at the start of the fixed 32 KiB NAPOT window `[0x60000, 0x68000)`
 * on Earl Grey Gen2 (32 KiB below the ECC-poisoned `rom_ctrl` digest words in
 * `[0x6FFE0, 0x70000)`).
 *
 * All payload offsets are computed at compile time via
 * `offsetof(fips_kat_rom_blob_t, data.<field>)`, eliminating any possibility
 * of cross-section linker padding drift.
 *
 * Uniform Binary Payload ABI Rule:
 * --------------------------------
 * Every variable-length byte slice inside `data[]` is individually padded with
 * trailing `0x00` bytes to a 4-byte boundary (`FIPS_KAT_ALIGN4(len)`). Every
 * sub-field begins on a 4-byte boundary for trap-free single-word loads on
 * RISC-V Ibex and UBSan-clean word access.
 * =============================================================================
 */


/**
 * Algorithm ID 1: SHA2-256
 * Schema: `hmac_kat_data_t`
 * Vector: key_len=0, msg_len=3 ("abc", pad4=4), digest_len=32
 */
typedef struct fips_kat_sha256 {
  uint32_t key_len;
  uint32_t msg_len;
  uint32_t digest_len;
  uint8_t data[36];
} fips_kat_sha256_t;

/**
 * Algorithm ID 2: SHA2-512
 * Schema: `hmac_kat_data_t`
 * Vector: key_len=0, msg_len=3 ("abc", pad4=4), digest_len=64
 */
typedef struct fips_kat_sha512 {
  uint32_t key_len;
  uint32_t msg_len;
  uint32_t digest_len;
  uint8_t data[68];
} fips_kat_sha512_t;

/**
 * Algorithm ID 3: HMAC-SHA2-256
 * Schema: `hmac_kat_data_t`
 * Vector: Non-uniform 32B key (0x00..0x1f), 50B msg (0x40..0x71, pad4=52), 32B
 * tag
 */
typedef struct fips_kat_hmac_sha256 {
  uint32_t key_len;
  uint32_t msg_len;
  uint32_t digest_len;
  uint8_t data[116];
} fips_kat_hmac_sha256_t;

/**
 * Algorithm ID 4: HMAC-SHA2-512
 * Schema: `hmac_kat_data_t`
 * Vector: Non-uniform 64B key (0x00..0x3f), 50B msg (0x40..0x71, pad4=52), 64B
 * tag
 */
typedef struct fips_kat_hmac_sha512 {
  uint32_t key_len;
  uint32_t msg_len;
  uint32_t digest_len;
  uint8_t data[180];
} fips_kat_hmac_sha512_t;

#define FIPS_KAT_NUM_ENTRIES 4

typedef struct fips_kat_rom_table {
  uint32_t magic;
  uint32_t version;
  uint32_t entry_count;
  uint32_t total_size;
  fips_kat_entry_t entries[FIPS_KAT_NUM_ENTRIES];
} fips_kat_rom_table_t;

typedef struct fips_kat_data_store {
  fips_kat_sha256_t sha256;
  fips_kat_sha512_t sha512;
  fips_kat_hmac_sha256_t hmac_sha256;
  fips_kat_hmac_sha512_t hmac_sha512;
} fips_kat_data_store_t;

/**
 * Single combined ROM blob containing both the descriptor table and all
 * contiguous vector payloads, pinned at `0x60000` in `.fips_kat`.
 */
typedef struct fips_kat_rom_blob {
  fips_kat_rom_table_t table;
  fips_kat_data_store_t data;
} fips_kat_rom_blob_t;

OT_ASSERT_MEMBER_OFFSET(fips_kat_rom_blob_t, table, 0);
static_assert(sizeof(fips_kat_rom_blob_t) % 4 == 0,
              "fips_kat_rom_blob_t must be 4-byte aligned in size");
static_assert(sizeof(fips_kat_rom_blob_t) <= kFipsKatRegionSize,
              "fips_kat_rom_blob_t exceeds 32 KiB NAPOT ROM window");

#define FIPS_KAT_OFFSET(field) \
  ((uint32_t)offsetof(fips_kat_rom_blob_t, data.field))

#ifdef OT_PLATFORM_RV32
OT_SECTION(".fips_kat")
#endif
OT_USED
alignas(uint32_t) static const fips_kat_rom_blob_t kFipsKatRomBlob = {
    .table =
        {
            .magic = kFipsKatDescriptorMagic,
            .version = kFipsKatDescriptorVersion1,
            .entry_count = FIPS_KAT_NUM_ENTRIES,
            .total_size = sizeof(fips_kat_rom_blob_t),
            .entries =
                {
                    {
                        .algorithm_id = (uint32_t)kFipsKatAlgSha2_256,
                        .offset = FIPS_KAT_OFFSET(sha256),
                        .size = sizeof(fips_kat_sha256_t),
                    },
                    {
                        .algorithm_id = (uint32_t)kFipsKatAlgSha2_512,
                        .offset = FIPS_KAT_OFFSET(sha512),
                        .size = sizeof(fips_kat_sha512_t),
                    },
                    {
                        .algorithm_id = (uint32_t)kFipsKatAlgHmacSha2_256,
                        .offset = FIPS_KAT_OFFSET(hmac_sha256),
                        .size = sizeof(fips_kat_hmac_sha256_t),
                    },
                    {
                        .algorithm_id = (uint32_t)kFipsKatAlgHmacSha2_512,
                        .offset = FIPS_KAT_OFFSET(hmac_sha512),
                        .size = sizeof(fips_kat_hmac_sha512_t),
                    },
                },
        },
    .data =
        {
            .sha256 = {
                .key_len = 0,
                .msg_len = 3,
                .digest_len = 32,
                .data = {
                    // Message "abc" (3 bytes + 1B pad)
                    0x61, 0x62, 0x63, 0x00,
                    // Expected SHA2-256 Digest (32 bytes)
                    0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
                    0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
                    0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
                    0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
                },
            },
            .sha512 = {
                .key_len = 0,
                .msg_len = 3,
                .digest_len = 64,
                .data = {
                    // Message "abc" (3 bytes + 1B pad)
                    0x61, 0x62, 0x63, 0x00,
                    // Expected SHA2-512 Digest (64 bytes)
                    0xdd, 0xaf, 0x35, 0xa1, 0x93, 0x61, 0x7a, 0xba,
                    0xcc, 0x41, 0x73, 0x49, 0xae, 0x20, 0x41, 0x31,
                    0x12, 0xe6, 0xfa, 0x4e, 0x89, 0xa9, 0x7e, 0xa2,
                    0x0a, 0x9e, 0xee, 0xe6, 0x4b, 0x55, 0xd3, 0x9a,
                    0x21, 0x92, 0x99, 0x2a, 0x27, 0x4f, 0xc1, 0xa8,
                    0x36, 0xba, 0x3c, 0x23, 0xa3, 0xfe, 0xeb, 0xbd,
                    0x45, 0x4d, 0x44, 0x23, 0x64, 0x3c, 0xe8, 0x0e,
                    0x2a, 0x9a, 0xc9, 0x4f, 0xa5, 0x4c, 0xa4, 0x9f,
                },
            },
            .hmac_sha256 = {
                .key_len = 32,
                .msg_len = 50,
                .digest_len = 32,
                .data = {
                    // Key (32 bytes)
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
                    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
                    0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
                    // Message (50 bytes + 2B pad)
                    0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47,
                    0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f,
                    0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57,
                    0x58, 0x59, 0x5a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f,
                    0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67,
                    0x68, 0x69, 0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f,
                    0x70, 0x71, 0x00, 0x00,
                    // Expected HMAC-SHA2-256 Tag (32 bytes)
                    0x20, 0x91, 0x24, 0x0b, 0xa2, 0xc6, 0xb2, 0x8a,
                    0x62, 0x57, 0x89, 0x25, 0xa6, 0x56, 0x47, 0x45,
                    0x1b, 0x0d, 0x45, 0x02, 0xe5, 0x61, 0xac, 0xbe,
                    0xcb, 0x7d, 0x25, 0xe7, 0x0e, 0x91, 0xcf, 0x1f,
                },
            },
            .hmac_sha512 = {
                .key_len = 64,
                .msg_len = 50,
                .digest_len = 64,
                .data = {
                    // Key (64 bytes)
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
                    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
                    0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
                    0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27,
                    0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f,
                    0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
                    0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f,
                    // Message (50 bytes + 2B pad)
                    0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47,
                    0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f,
                    0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57,
                    0x58, 0x59, 0x5a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f,
                    0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67,
                    0x68, 0x69, 0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f,
                    0x70, 0x71, 0x00, 0x00,
                    // Expected HMAC-SHA2-512 Tag (64 bytes)
                    0xfc, 0x54, 0xf2, 0x35, 0x81, 0xaa, 0xe0, 0x38,
                    0xe6, 0x46, 0x3a, 0x63, 0xbf, 0xda, 0xf9, 0x9b,
                    0xb7, 0x7a, 0x61, 0x53, 0x2e, 0xfd, 0xe0, 0xf8,
                    0x0c, 0x90, 0x0f, 0xc9, 0x48, 0x4e, 0x8b, 0xcb,
                    0xdc, 0x37, 0x5b, 0x73, 0x26, 0x0e, 0x92, 0x00,
                    0xb0, 0x8e, 0x5e, 0x7b, 0x6b, 0x8a, 0x2a, 0x3e,
                    0x0c, 0xda, 0x68, 0xeb, 0xb3, 0xb8, 0xd7, 0x45,
                    0xed, 0xd3, 0xae, 0xe4, 0xc2, 0x4a, 0xdd, 0x1c,
                },
            },
        },
};

#ifndef OT_PLATFORM_RV32
const fips_kat_descriptor_table_t *fips_kat_get_rom_table_for_host_test(void) {
  return (const fips_kat_descriptor_table_t *)&kFipsKatRomBlob.table;
}
#endif
