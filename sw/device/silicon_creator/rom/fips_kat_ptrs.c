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
 * Optimization & Footprint Architecture:
 * -------------------------------------
 * ROM space is strictly constrained (~192 KB total, shared with boot
 * logic, chip info, and silicon creator keys). Full raw FIPS 140-3 test
 * vectors would consume >35 KB. To fit within our ~11.9 KB budget, vectors
 * utilize standardized optimization techniques:
 *
 * 1. Minimal Message Size (MMS):
 *    Uses the shortest NIST-approved message length (e.g. 3-byte "abc" for
 *    SHA2-256, 12-byte messages for HMAC) that exercises full message
 *    padding, block scheduling, compression loop, and digest finalization.
 *
 * 2. Single-Vector Parameterization (SVP):
 *    A single operational vector validates multiple related modes (e.g. AES
 *    encryption vectors that test key scheduling and S-boxes also validate
 *    decryption; AES-256 validation covers 128/192 bit algorithmic paths;
 *    zero-payload AAD/IV reuse in AES-GCM).
 *
 * 3. Deterministic Key Generation (DKG):
 *    Instead of storing multi-kilobyte public/private key pairs, stores a
 *    32-byte PRNG seed. The test runner deterministically derives the keypair
 *    in RAM prior to execution.
 *
 * 4. Output Hashing (OH):
 *    For asymmetric algorithms with large signatures (e.g. RSA-4096, ML-DSA)
 *    or ciphertexts/shared secrets, stores only the 32-byte SHA2-256 digest
 *    of the expected output.
 *
 * 5. Dynamic Sign-then-Verify (DSV) & Dynamic Encap/Decap (DED):
 *    The test runner signs or encapsulates dynamically, hashes the output to
 *    verify correctness, and immediately passes the generated artifact into
 *    the verification or decapsulation routine, exercising both paths with
 *    zero additional ROM overhead.
 *
 * Ibex Alignment Rule:
 * -------------------
 * All test vector payload structures must have a `sizeof` that is a multiple
 * of 4 bytes, and all sub-fields must be 4-byte naturally aligned to ensure
 * single-word load efficiency on RISC-V Ibex without trap penalties.
 * =============================================================================
 */

/**
 * Concrete test vector structure for SHA2-256 pilot vector.
 *
 * Schema: `hmac_kat_data_t` equivalent.
 * Optimization: Minimal Message Size (MMS).
 *
 * How this vector is built:
 * - Key Length (`key_len`): 0 bytes (pure hash mode, no HMAC key).
 * - Message Length (`msg_len`): 3 bytes (ASCII string "abc").
 * - Digest Length (`digest_len`): 32 bytes (256-bit SHA2-256 digest).
 * - Data Array (`data`): Contiguous payload holding:
 *     [0 .. 2]   : Message bytes ('a', 'b', 'c')
 *     [3 .. 34]  : Expected SHA2-256 digest (32 bytes)
 * - Padding (`padding`): 1 byte to ensure 4-byte natural alignment.
 * - Total ROM Footprint: 12 bytes (header) + 35 bytes (data) + 1 byte (pad)
 *                       = 48 bytes.
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgSha2_256`.
 * 2. Dereference as `const hmac_kat_data_t *kat = get_fips_data(table, entry)`.
 * 3. Verify `kat->key_len == 0` (indicating pure hash, not keyed HMAC).
 * 4. Locate message: `const uint8_t *msg = kat->data + kat->key_len`.
 * 5. Locate expected digest:
 *      `const uint8_t *expected = kat->data + kat->key_len + kat->msg_len`.
 * 6. Compute SHA2-256 on `msg` (length `kat->msg_len`) using the hardware HMAC
 *    accelerator or software SHA2 driver.
 * 7. Compare calculated 32-byte digest against `expected`.
 */
typedef struct fips_kat_sha256_pilot {
  uint32_t key_len;
  uint32_t msg_len;
  uint32_t digest_len;
  uint8_t data[35];
  uint8_t padding[1];  // 4-byte natural alignment
} fips_kat_sha256_pilot_t;

/**
 * Concrete test vector structure for HMAC-SHA2-256 (Algorithm ID 11).
 *
 * Schema: `hmac_kat_data_t` equivalent.
 * Optimization: Minimal Message Size (MMS).
 *
 * How this vector was obtained:
 * - Authoritative Reference: RFC 4231 Test Case 3 / NIST CAVP HMAC-SHA256.
 * - Key: 32 bytes (256-bit key: 0xaa repeated 32 times).
 * - Message: 50 bytes (0xdd repeated 50 times).
 * - Expected Digest: 32 bytes (256-bit HMAC tag:
 *   cdcb1220d1ecccea91e53aba3092f962e549fe6ce9ed7fdc43191fbde45c30b0).
 *
 * How inputs/outputs were transformed:
 * - Contiguous Payload: Key (32 bytes) + Message (50 bytes) + Digest (32 bytes)
 *   = 114 bytes.
 * - Ibex Alignment: 2 bytes of trailing zero-padding (`padding[2]`) added to
 *   achieve strict 4-byte natural alignment (114 + 2 = 116 bytes payload,
 *   total `sizeof(fips_kat_hmac_sha256_t) == 128` bytes).
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgHmacSha2_256`.
 * 2. Dereference as `const hmac_kat_data_t *kat = get_fips_data(table, entry)`.
 * 3. Extract key: `const uint8_t *key = kat->data` (length `kat->key_len` =
 * 32).
 * 4. Extract message: `const uint8_t *msg = kat->data + kat->key_len` (length
 * `kat->msg_len` = 50).
 * 5. Extract expected tag: `const uint8_t *expected = kat->data + kat->key_len
 * + kat->msg_len`.
 * 6. Pack key into `hmac_key_t` and invoke hardware `sc_hmac_hmac_sha256` or
 * cryptolib driver.
 * 7. Compare calculated 32-byte MAC against `expected`.
 */
typedef struct fips_kat_hmac_sha256 {
  uint32_t key_len;
  uint32_t msg_len;
  uint32_t digest_len;
  uint8_t data[114];
  uint8_t padding[2];  // 4-byte natural alignment
} fips_kat_hmac_sha256_t;

/**
 * Concrete test vector structure for SHA2-512 (Algorithm ID 10).
 *
 * Schema: `hmac_kat_data_t` equivalent.
 * Optimization: Minimal Message Size (MMS).
 *
 * How this vector was obtained:
 * - Authoritative Reference: NIST FIPS 180-4 / NIST CAVP SHA-512 Test Vector
 * #1.
 * - Message: ASCII "abc" (3 bytes: 0x61, 0x62, 0x63).
 * - Expected Digest: 64 bytes (512-bit SHA-512 digest:
 *   ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a
 *   2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f).
 *
 * How inputs/outputs were transformed:
 * - Pure Hash Mode: key_len = 0 (no HMAC key).
 * - Contiguous Payload: Message (3 bytes) + Digest (64 bytes) = 67 bytes.
 * - Ibex Alignment: 1 byte of trailing zero-padding (`padding[1]`) added to
 *   achieve strict 4-byte natural alignment (67 + 1 = 68 bytes payload,
 *   total `sizeof(fips_kat_sha512_t) == 80` bytes: 12 bytes header + 68 bytes).
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgSha2_512`.
 * 2. Dereference as `const hmac_kat_data_t *kat = get_fips_data(table, entry)`.
 * 3. Extract message: `const uint8_t *msg = kat->data + kat->key_len` (length
 * `kat->msg_len` = 3).
 * 4. Extract expected digest: `const uint8_t *expected = kat->data +
 * kat->key_len + kat->msg_len` (length `kat->digest_len` = 64).
 * 5. Configure HMAC peripheral for SHA2-512 mode
 * (`HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_512`), process, and read 16 digest words
 * (`HMAC_DIGEST_0` through `HMAC_DIGEST_15`).
 * 6. Compare computed 64-byte digest against `expected`.
 */
typedef struct fips_kat_sha512 {
  uint32_t key_len;
  uint32_t msg_len;
  uint32_t digest_len;
  uint8_t data[67];
  uint8_t padding[1];  // 4-byte natural alignment
} fips_kat_sha512_t;

/**
 * Concrete test vector structure for HMAC-SHA2-512 (Algorithm ID 12).
 *
 * Schema: `hmac_kat_data_t` equivalent.
 * Optimization: Minimal Message Size (MMS).
 *
 * How this vector was obtained:
 * - Authoritative Reference: RFC 4231 Test Case 3 / NIST CAVP HMAC-SHA512.
 * - Key: 20 bytes (160-bit key: 0xaa repeated 20 times).
 * - Message: 50 bytes (0xdd repeated 50 times).
 * - Expected Digest: 64 bytes (512-bit HMAC tag:
 *   fa73b0089d56a284efb0f0756c890be9b1b5dbdd8ee81a3655f83e33b2279d39
 *   bf3e848279a722c806b485a47e67c807b946a337bee8942674278859e13292fb).
 *
 * How inputs/outputs were transformed:
 * - Contiguous Payload: Key (20 bytes) + Message (50 bytes) + Digest (64 bytes)
 *   = 134 bytes.
 * - Ibex Alignment: 2 bytes of trailing zero-padding (`padding[2]`) added to
 *   achieve strict 4-byte natural alignment (134 + 2 = 136 bytes payload,
 *   total `sizeof(fips_kat_hmac_sha512_t) == 148` bytes: 12 bytes header + 136
 * bytes).
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgHmacSha2_512`.
 * 2. Dereference as `const hmac_kat_data_t *kat = get_fips_data(table, entry)`.
 * 3. Extract key: `const uint8_t *key = kat->data` (length `kat->key_len` =
 * 20).
 * 4. Extract message: `const uint8_t *msg = kat->data + kat->key_len` (length
 * `kat->msg_len` = 50).
 * 5. Extract expected tag: `const uint8_t *expected = kat->data + kat->key_len
 * + kat->msg_len` (length `kat->digest_len` = 64).
 * 6. Zero-pad key to 1024-bit block size into `uint32_t key_block[32]`,
 * configure HMAC IP for HMAC-SHA2-512 with `kKeyLength1024` and
 * `kDigestLengthSha512`.
 * 7. Write key to `HMAC_KEY_0`..`HMAC_KEY_31`, start hash, write message bytes
 * to `HMAC_MSG_FIFO`, trigger process, wait for done.
 * 8. Read 16 digest registers (`HMAC_DIGEST_0` through `HMAC_DIGEST_15`) and
 * compare with `expected`.
 */
typedef struct fips_kat_hmac_sha512 {
  uint32_t key_len;
  uint32_t msg_len;
  uint32_t digest_len;
  uint8_t data[134];
  uint8_t padding[2];  // 4-byte natural alignment
} fips_kat_hmac_sha512_t;

/**
 * Container holding all embedded FIPS KAT vector payloads in `.fips_kat.data`.
 */
typedef struct fips_kat_data_store {
  fips_kat_sha256_pilot_t sha256_pilot;
  fips_kat_hmac_sha256_t hmac_sha256;
  fips_kat_sha512_t sha512;
  fips_kat_hmac_sha512_t hmac_sha512;
} fips_kat_data_store_t;

/**
 * FIPS KAT vector data payload placed in `.fips_kat.data`.
 */
OT_SECTION(".fips_kat.data")
OT_USED
alignas(uint32_t) static const fips_kat_data_store_t kFipsKatDataStore = {
    .sha256_pilot =
        {
            .key_len = 0,
            .msg_len = 3,
            .digest_len = 32,
            .data =
                {
                    'a',  'b',  'c',  0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01,
                    0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22,
                    0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
                    0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
                },
            .padding = {0},
        },
    .hmac_sha256 =
        {
            .key_len = 32,
            .msg_len = 50,
            .digest_len = 32,
            .data =
                {
                    // Key (32 bytes of 0xaa)
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    // Message (50 bytes of 0xdd)
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    // Expected Digest (32 bytes)
                    0xcd,
                    0xcb,
                    0x12,
                    0x20,
                    0xd1,
                    0xec,
                    0xcc,
                    0xea,
                    0x91,
                    0xe5,
                    0x3a,
                    0xba,
                    0x30,
                    0x92,
                    0xf9,
                    0x62,
                    0xe5,
                    0x49,
                    0xfe,
                    0x6c,
                    0xe9,
                    0xed,
                    0x7f,
                    0xdc,
                    0x43,
                    0x19,
                    0x1f,
                    0xbd,
                    0xe4,
                    0x5c,
                    0x30,
                    0xb0,
                },
            .padding = {0, 0},
        },
    .sha512 =
        {
            .key_len = 0,
            .msg_len = 3,
            .digest_len = 64,
            .data =
                {
                    'a',
                    'b',
                    'c',
                    // Expected Digest (64 bytes)
                    0xdd,
                    0xaf,
                    0x35,
                    0xa1,
                    0x93,
                    0x61,
                    0x7a,
                    0xba,
                    0xcc,
                    0x41,
                    0x73,
                    0x49,
                    0xae,
                    0x20,
                    0x41,
                    0x31,
                    0x12,
                    0xe6,
                    0xfa,
                    0x4e,
                    0x89,
                    0xa9,
                    0x7e,
                    0xa2,
                    0x0a,
                    0x9e,
                    0xee,
                    0xe6,
                    0x4b,
                    0x55,
                    0xd3,
                    0x9a,
                    0x21,
                    0x92,
                    0x99,
                    0x2a,
                    0x27,
                    0x4f,
                    0xc1,
                    0xa8,
                    0x36,
                    0xba,
                    0x3c,
                    0x23,
                    0xa3,
                    0xfe,
                    0xeb,
                    0xbd,
                    0x45,
                    0x4d,
                    0x44,
                    0x23,
                    0x64,
                    0x3c,
                    0xe8,
                    0x0e,
                    0x2a,
                    0x9a,
                    0xc9,
                    0x4f,
                    0xa5,
                    0x4c,
                    0xa4,
                    0x9f,
                },
            .padding = {0},
        },
    .hmac_sha512 =
        {
            .key_len = 20,
            .msg_len = 50,
            .digest_len = 64,
            .data =
                {
                    // Key (20 bytes of 0xaa)
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    0xaa,
                    // Message (50 bytes of 0xdd)
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    0xdd,
                    // Expected Digest (64 bytes)
                    0xfa,
                    0x73,
                    0xb0,
                    0x08,
                    0x9d,
                    0x56,
                    0xa2,
                    0x84,
                    0xef,
                    0xb0,
                    0xf0,
                    0x75,
                    0x6c,
                    0x89,
                    0x0b,
                    0xe9,
                    0xb1,
                    0xb5,
                    0xdb,
                    0xdd,
                    0x8e,
                    0xe8,
                    0x1a,
                    0x36,
                    0x55,
                    0xf8,
                    0x3e,
                    0x33,
                    0xb2,
                    0x27,
                    0x9d,
                    0x39,
                    0xbf,
                    0x3e,
                    0x84,
                    0x82,
                    0x79,
                    0xa7,
                    0x22,
                    0xc8,
                    0x06,
                    0xb4,
                    0x85,
                    0xa4,
                    0x7e,
                    0x67,
                    0xc8,
                    0x07,
                    0xb9,
                    0x46,
                    0xa3,
                    0x37,
                    0xbe,
                    0xe8,
                    0x94,
                    0x26,
                    0x74,
                    0x27,
                    0x88,
                    0x59,
                    0xe1,
                    0x32,
                    0x92,
                    0xfb,
                },
            .padding = {0, 0},
        },
};

/**
 * Macro computing exact byte offset of a vector payload from
 * the start of `kFipsKatDescriptorTable`.
 */
#define FIPS_KAT_OFFSET(field) \
  (sizeof(fips_kat_rom_table_t) + offsetof(fips_kat_data_store_t, field))

/**
 * Concrete descriptor table in ROM holding 4 entries.
 */
#define FIPS_KAT_NUM_ENTRIES 4

/**
 * Concrete descriptor table in ROM holding 4 entries.
 */
typedef struct fips_kat_rom_table {
  uint32_t magic;
  uint32_t version;
  uint32_t entry_count;
  uint32_t total_size;
  fips_kat_entry_t entries[FIPS_KAT_NUM_ENTRIES];
} fips_kat_rom_table_t;

OT_SECTION(".fips_kat.table")
OT_USED
alignas(uint32_t) static const fips_kat_rom_table_t kFipsKatDescriptorTable = {
    .magic = kFipsKatDescriptorMagic,
    .version = kFipsKatDescriptorVersion1,
    .entry_count = FIPS_KAT_NUM_ENTRIES,
    .total_size = sizeof(fips_kat_rom_table_t) + sizeof(fips_kat_data_store_t),
    .entries =
        {
            {
                .algorithm_id = (uint32_t)kFipsKatAlgSha2_256,
                .offset = FIPS_KAT_OFFSET(sha256_pilot),
                .size = sizeof(fips_kat_sha256_pilot_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgHmacSha2_256,
                .offset = FIPS_KAT_OFFSET(hmac_sha256),
                .size = sizeof(fips_kat_hmac_sha256_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgSha2_512,
                .offset = FIPS_KAT_OFFSET(sha512),
                .size = sizeof(fips_kat_sha512_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgHmacSha2_512,
                .offset = FIPS_KAT_OFFSET(hmac_sha512),
                .size = sizeof(fips_kat_hmac_sha512_t),
            },
        },
};

/**
 * Fixed pointer to the FIPS KAT descriptor table placed at
 * `_rom_chip_info_start - 4`.
 */
OT_SECTION(".fips_kat_descriptor_ptr")
OT_USED
const fips_kat_descriptor_table_t *const kFipsKatDescriptorPtr =
    (const fips_kat_descriptor_table_t *)&kFipsKatDescriptorTable;
