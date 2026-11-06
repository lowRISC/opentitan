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
 * Algorithm 6: SHAKE-256 (Alg ID 15)
 *
 * Source Standard: NIST FIPS 202 (SHA-3 Standard: Permutation-Based Hash and
 * Extendable-Output Functions) / CAVP ShortMsg Test Vector.
 *
 * Test Vector Parameters:
 * - Key: None (0 bytes).
 * - Message: 1 byte (`0x0f`).
 * - Requested Squeeze Length: 32 bytes (256 bits).
 * - Expected Squeezed Output (32 bytes):
 *   aabb07488ff9edd05d6a603b7791b60a16d45093608f1badc0c9cc9a9154f215
 *
 * How inputs/outputs were transformed:
 * - Header Fields:
 *     key_len    = 0  (no key for SHAKE-256)
 *     msg_len    = 1  (1-byte input message)
 *     digest_len = 32 (32-byte squeezed output length)
 * - Contiguous Payload:
 *     data[0..3]   = {0x0f, 0x00, 0x00, 0x00} (1-byte msg + 3-byte 0x00 padding
 * for 4-byte Ibex word alignment) data[4..35]  = 32-byte expected squeezed
 * digest
 * - Ibex Alignment: 12 bytes (header: 3 x uint32_t) + 36 bytes (payload)
 *   = 48 bytes total (`48 % 4 == 0`).
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgShake256`.
 * 2. Dereference as `const hmac_kat_data_t *kat = get_fips_data(table, entry)`.
 * 3. Verify parameters: `kat->key_len == 0`, `kat->msg_len == 1`,
 * `kat->digest_len == 32`.
 * 4. Extract pointers:
 *      `const uint8_t *msg = kat->data + kat->key_len;`
 *      `const uint8_t *expected_digest = kat->data + kat->key_len +
 * ((kat->msg_len + 3) & ~3u);`
 * 5. Configure KMAC IP in SHAKE-256 mode via `kmac_shake256_configure()`.
 * 6. Start hashing via `kmac_shake256_start()`, absorb 1 byte via
 * `kmac_shake256_absorb(msg, 1)`.
 * 7. Transition to squeezing via `kmac_shake256_squeeze_start()`.
 * 8. Squeeze 8 words (32 bytes) via `kmac_shake256_squeeze_end(digest_words,
 * 8)`.
 * 9. Compare computed digest against `expected_digest`.
 */
typedef struct fips_kat_shake256 {
  uint32_t key_len;
  uint32_t msg_len;
  uint32_t digest_len;
  uint8_t data[36];
} fips_kat_shake256_t;

/**
 * Algorithm 7: KMAC-256 (Alg ID 14)
 *
 * Source Standard: NIST SP 800-185 (SHA-3 Derived Functions: cSHAKE, KMAC,
 * TupleHash, and ParallelHash) / Section 8.4.2 Sample #1 / CAVP Vector.
 *
 * Test Vector Parameters:
 * - Key: 32 bytes (256-bit:
 * 404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f).
 * - Message: 4 bytes (00010203).
 * - Customization String (S): "My Tagged Application" (21 bytes).
 * - Requested Squeeze Length: 64 bytes (512 bits).
 * - Expected Squeezed Output (64 bytes):
 *   20c570c31346f703c9ac36c61c03cb64c3970d0cfc787e9b79599d273a68d2f7
 *   f69d4cc3de9d104a351689f27cf6f5951f0103f33f4f24871024d9c27773a8dd
 *
 * How inputs/outputs were transformed:
 * - Header Fields:
 *     key_len    = 32 (32-byte KMAC key)
 *     msg_len    = 4  (4-byte input message)
 *     digest_len = 64 (64-byte squeezed output length)
 * - Contiguous Payload:
 *     data[0..31]  = 32-byte key
 *     data[32..35] = 4-byte message (0x00, 0x01, 0x02, 0x03)
 *     data[36..99] = 64-byte expected output
 * - Ibex Alignment: 12 bytes (header: 3 x uint32_t) + 100 bytes (payload)
 *   = 112 bytes total (`112 % 4 == 0`). Naturally 4-byte aligned, 0 padding
 * bytes.
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgKmac256`.
 * 2. Dereference as `const hmac_kat_data_t *kat = get_fips_data(table, entry)`.
 * 3. Verify parameters: `kat->key_len == 32`, `kat->msg_len == 4`,
 * `kat->digest_len == 64`.
 * 4. Extract pointers:
 *      `const uint8_t *key = kat->data;`
 *      `const uint8_t *msg = kat->data + kat->key_len;`
 *      `const uint8_t *expected_digest = kat->data + kat->key_len +
 * kat->msg_len;`
 * 5. Configure KMAC IP in KMAC-256 mode via `kmac_kmac256_sw_configure()`.
 * 6. Load software key via `kmac_kmac256_sw_key((const uint32_t *)key, 8)`.
 * 7. Set customization prefix: `kmac_kmac256_set_prefix("My Tagged
 * Application", 21)`.
 * 8. Start hashing via `kmac_kmac256_start()`, absorb message via
 * `kmac_kmac256_absorb(msg, 4)`.
 * 9. Squeeze 16 words (64 bytes) via `kmac_kmac256_final(digest_words, 16)`.
 * 10. Compare computed digest against `expected_digest`.
 */
typedef struct fips_kat_kmac256 {
  uint32_t key_len;
  uint32_t msg_len;
  uint32_t digest_len;
  uint8_t data[100];
} fips_kat_kmac256_t;

/**
 * Concrete test vector structure for AES-256-ECB Decrypt (Algorithm ID 2).
 *
 * Schema: `aes_kat_data_t` equivalent.
 * Optimization: Single-Vector Parameterization (SVP), Single-Block Reuse.
 *
 * How this vector was obtained:
 * - Authoritative Reference: NIST SP 800-38A Section F.1.5 (ECB-AES256) /
 *   NIST CAVP / ACVP Vector Set 3483386 Test Case 21.
 * - Key: 32 bytes (256-bit key:
 *   603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4).
 * - Plaintext: 16 bytes (128-bit block 1:
 *   6bc1bee22e409f96e93d7e117393172a).
 * - Ciphertext: 16 bytes (128-bit block 1:
 *   f3eed1bdb5d2a03c064b5a7e3db181f8).
 *
 * How inputs/outputs were transformed:
 * - Header Fields:
 *     key_len = 32
 *     iv_len  = 0  (ECB mode does not utilize an initialization vector)
 *     aad_len = 0  (ECB mode does not utilize additional authenticated data)
 *     pt_len  = 16 (16-byte decrypted plaintext)
 *     ct_len  = 16 (16-byte encrypted ciphertext input)
 *     tag_len = 0  (ECB mode has no authentication tag)
 * - Contiguous Payload: Key (32 bytes) + Plaintext (16 bytes) +
 *   Ciphertext (16 bytes) = 64 bytes.
 * - Ibex Alignment: 24 bytes (header: 6 x uint32_t) + 64 bytes (payload)
 *   = 88 bytes total (`88 % 4 == 0`). Naturally 4-byte aligned, 0 padding
 * bytes.
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgAesEcb256Decrypt`.
 * 2. Dereference as `const aes_kat_data_t *kat = get_fips_data(table, entry)`.
 * 3. Verify parameters: `kat->key_len == 32`, `kat->iv_len == 0`, `kat->aad_len
 * == 0`, `kat->pt_len == 16`, `kat->ct_len == 16`, `kat->tag_len == 0`.
 * 4. Extract pointers:
 *      `const uint8_t *key = kat->data;`
 *      `const uint8_t *expected_pt = kat->data + kat->key_len;`
 *      `const uint8_t *ct = kat->data + kat->key_len + kat->pt_len;`
 * 5. Configure hardware AES IP in automatic decrypt mode:
 *      operation = `kDifAesOperationDecrypt`,
 *      mode = `kDifAesModeEcb`,
 *      key_len = `kDifAesKey256`.
 * 6. Split/mask 32-byte key into two 256-bit key shares (`share0 = key`,
 * `share1 = 0`), start transaction, load 16-byte ciphertext block into AES IP.
 * 7. Read 16-byte decrypted output block and compare against `expected_pt`.
 */
typedef struct fips_kat_aes_ecb256 {
  uint32_t key_len;
  uint32_t iv_len;
  uint32_t aad_len;
  uint32_t pt_len;
  uint32_t ct_len;
  uint32_t tag_len;
  uint8_t data[64];
} fips_kat_aes_ecb256_t;

/**
 * Algorithm 10: AES-256-CBC Decrypt (Alg ID 4)
 *
 * Source Standard: NIST SP 800-38A (Recommendation for Block Cipher Modes of
 * Operation: Methods and Techniques) Section F.2.5 (CBC-AES256) / CAVP / ACVP.
 *
 * Test Vector Parameters:
 * - Key: 32 bytes (256-bit key:
 * 603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4).
 * - IV: 16 bytes (128-bit IV: 000102030405060708090a0b0c0d0e0f).
 * - Plaintext: 16 bytes (128-bit block 1: 6bc1bee22e409f96e93d7e117393172a).
 * - Ciphertext: 16 bytes (128-bit block 1: f58c4c04d6e5f1ba779eabfb5f7bfbd6).
 *
 * How inputs/outputs were transformed:
 * - Header Fields:
 *     key_len = 32 (32-byte 256-bit key)
 *     iv_len  = 16 (16-byte initialization vector)
 *     aad_len = 0  (CBC mode does not utilize additional authenticated data)
 *     pt_len  = 16 (16-byte decrypted plaintext output)
 *     ct_len  = 16 (16-byte encrypted ciphertext input)
 *     tag_len = 0  (CBC mode has no authentication tag)
 * - Contiguous Payload: Key (32 bytes) + IV (16 bytes) + Plaintext (16 bytes) +
 *   Ciphertext (16 bytes) = 80 bytes.
 * - Ibex Alignment: 24 bytes (header: 6 x uint32_t) + 80 bytes (payload)
 *   = 104 bytes total (`104 % 4 == 0`). Naturally 4-byte aligned, 0 padding
 * bytes.
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgAesCbc256Decrypt`.
 * 2. Dereference as `const aes_kat_data_t *kat = get_fips_data(table, entry)`.
 * 3. Verify parameters: `kat->key_len == 32`, `kat->iv_len == 16`,
 * `kat->aad_len == 0`, `kat->pt_len == 16`, `kat->ct_len == 16`, `kat->tag_len
 * == 0`.
 * 4. Extract pointers:
 *      `const uint8_t *key = kat->data;`
 *      `const uint8_t *iv = kat->data + kat->key_len;`
 *      `const uint8_t *expected_pt = kat->data + kat->key_len + kat->iv_len;`
 *      `const uint8_t *ct = kat->data + kat->key_len + kat->iv_len +
 * kat->pt_len;`
 * 5. Configure hardware AES IP in automatic decrypt mode:
 *      operation = `kDifAesOperationDecrypt`,
 *      mode = `kDifAesModeCbc`,
 *      key_len = `kDifAesKey256`.
 * 6. Split/mask 32-byte key into two 256-bit key shares (`share0 = key`,
 * `share1 = 0`), load IV, start transaction, load 16-byte ciphertext block into
 * AES IP.
 * 7. Read 16-byte decrypted output block and compare against `expected_pt`.
 */
typedef struct fips_kat_aes_cbc256 {
  uint32_t key_len;
  uint32_t iv_len;
  uint32_t aad_len;
  uint32_t pt_len;
  uint32_t ct_len;
  uint32_t tag_len;
  uint8_t data[80];
} fips_kat_aes_cbc256_t;

/**
 * Algorithm 14: AES-KWP-256 Wrap / Key Wrap with Padding (Alg ID 8)
 *
 * Source Standard: NIST SP 800-38F (Section 6.3, Algorithm 5 / 6) & RFC 5649 /
 * CAVP.
 *
 * Test Vector Parameters:
 * - Key (KEK): 32 bytes (256-bit:
 * 603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4).
 * - Plaintext: 16 bytes (128-bit: 6bc1bee22e409f96e93d7e117393172a).
 * - Ciphertext (Wrapped Output): 24 bytes (192-bit:
 * cc06ca9ed08db03213481e0b440d7fabf8850cccad630053).
 *
 * How inputs/outputs were transformed:
 * - Header Fields:
 *     key_len = 32 (256-bit KEK)
 *     iv_len  = 0
 *     aad_len = 0
 *     pt_len  = 16 (16-byte key material to wrap)
 *     ct_len  = 24 (24-byte wrapped ciphertext with 64-bit ICV)
 *     tag_len = 0
 * - Contiguous Payload:
 *     data[0..31]  = 32-byte KEK
 *     data[32..47] = 16-byte plaintext key material
 *     data[48..71] = 24-byte expected wrapped ciphertext
 * - Ibex Alignment: 24 bytes (header: 6 x uint32_t) + 72 bytes (payload)
 *   = 96 bytes total (`96 % 4 == 0`). Naturally 4-byte aligned.
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgAesKwp256Wrap`.
 * 2. Dereference as `const aes_kat_data_t *kat = get_fips_data(table, entry)`.
 * 3. Verify parameters: `kat->key_len == 32`, `kat->pt_len == 16`, `kat->ct_len
 * == 24`.
 * 4. Extract pointers:
 *      `const uint8_t *kek = kat->data;`
 *      `const uint8_t *pt = kat->data + kat->key_len;`
 *      `const uint8_t *expected_ct = kat->data + kat->key_len + kat->pt_len;`
 * 5. Execute AES-KWP wrapping via hardware AES accelerator in ECB mode (NIST SP
 * 800-38F Alg 5).
 * 6. Compare computed ciphertext against `expected_ct`.
 * 7. Optionally execute AES-KWP unwrapping (Alg 6) and verify recovered
 * plaintext equals `pt`.
 */
typedef struct fips_kat_aes_kwp256 {
  uint32_t key_len;
  uint32_t iv_len;
  uint32_t aad_len;
  uint32_t pt_len;
  uint32_t ct_len;
  uint32_t tag_len;
  uint8_t data[72];
} fips_kat_aes_kwp256_t;

/**
 * Algorithm 12: KDF-HMAC-SHA2-256 (Alg ID 37)
 *
 * Source Standard: NIST SP 800-108r1 (Recommendation for Key Derivation Using
 * Pseudorandom Functions) Section 4.1 (Counter Mode) / CAVP / ACVP.
 *
 * Test Vector Parameters:
 * - Key (KDK): 32 bytes (256-bit key: 0x0b repeated 32 times).
 * - Label: 6 bytes (0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5).
 * - Separator: 1 byte (0x00).
 * - Context: 6 bytes (0x60, 0x61, 0x62, 0x63, 0x64, 0x65).
 * - Counter `[i]_2`: 4 bytes (0x00, 0x00, 0x00, 0x01).
 * - Length `[L]_2`: 4 bytes (0x00, 0x00, 0x01, 0x00 = 256 bits).
 * - Formatted Message: 21 bytes:
 *   [i]_2 || Label || 0x00 || Context || [L]_2
 *   = 00000001 b0b1b2b3b4b5 00 606162636465 00000100
 * - Expected Derived Keying Material (32 bytes = 256 bits):
 *   12b44b700276c03074cd99f98763574b7bf71c30340223790bf0b8f53fcf3c86
 *
 * How inputs/outputs were transformed:
 * - Header Fields:
 *     key_len    = 32 (32-byte KDK)
 *     msg_len    = 21 (21-byte formatted counter-mode message)
 *     digest_len = 32 (32-byte derived keying material output)
 * - Contiguous Payload:
 *     data[0..31]  = 32-byte KDK
 *     data[32..52] = 21-byte formatted input message
 *     data[53..55] = 3 bytes 0x00 padding for 4-byte Ibex word alignment
 *     data[56..87] = 32-byte expected derived keying material
 * - Ibex Alignment: 12 bytes (header: 3 x uint32_t) + 88 bytes (payload)
 *   = 100 bytes total (`100 % 4 == 0`). Naturally 4-byte aligned.
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgKdfHmacSha2_256`.
 * 2. Dereference as `const hmac_kat_data_t *kat = get_fips_data(table, entry)`.
 * 3. Verify parameters: `kat->key_len == 32`, `kat->msg_len == 21`,
 * `kat->digest_len == 32`.
 * 4. Extract pointers:
 *      `const uint8_t *kdk = kat->data;`
 *      `const uint8_t *msg = kat->data + kat->key_len;`
 *      `const uint8_t *expected_km = kat->data + kat->key_len + ((kat->msg_len
 * + 3) & ~3u);`
 * 5. Compute HMAC-SHA2-256 on `msg` using key `kdk` via hardware HMAC
 * accelerator.
 * 6. Compare computed output against `expected_km`.
 */
typedef struct fips_kat_kdf_hmac_sha256 {
  uint32_t key_len;
  uint32_t msg_len;
  uint32_t digest_len;
  uint8_t data[88];
} fips_kat_kdf_hmac_sha256_t;

/**
 * Algorithm 13: KDF-KMAC-256 (Alg ID 38)
 *
 * Source Standard: NIST SP 800-108r1 / NIST SP 800-185 (Section 8.4.2 Sample
 * #1) / CAVP Vector.
 *
 * Test Vector Parameters:
 * - Key (KDK): 32 bytes (256-bit:
 * 404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f).
 * - Context (Message): 4 bytes (00010203).
 * - Label (Customization String S): "My Tagged Application" (21 bytes).
 * - Output Length: 64 bytes (512 bits).
 * - Expected Keying Material (64 bytes):
 *   20c570c31346f703c9ac36c61c03cb64c3970d0cfc787e9b79599d273a68d2f7
 *   f69d4cc3de9d104a351689f27cf6f5951f0103f33f4f24871024d9c27773a8dd
 *
 * How inputs/outputs were transformed:
 * - Header Fields:
 *     key_len    = 32 (32-byte KDK)
 *     msg_len    = 4  (4-byte context/message)
 *     digest_len = 64 (64-byte derived keying material output)
 * - Contiguous Payload:
 *     data[0..31]  = 32-byte KDK
 *     data[32..35] = 4-byte context/message (0x00, 0x01, 0x02, 0x03)
 *     data[36..99] = 64-byte expected output
 * - Ibex Alignment: 12 bytes (header: 3 x uint32_t) + 100 bytes (payload)
 *   = 112 bytes total (`112 % 4 == 0`). Naturally 4-byte aligned.
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgKdfKmac256`.
 * 2. Dereference as `const hmac_kat_data_t *kat = get_fips_data(table, entry)`.
 * 3. Verify parameters: `kat->key_len == 32`, `kat->msg_len == 4`,
 * `kat->digest_len == 64`.
 * 4. Extract pointers:
 *      `const uint8_t *kdk = kat->data;`
 *      `const uint8_t *context = kat->data + kat->key_len;`
 *      `const uint8_t *expected_km = kat->data + kat->key_len + kat->msg_len;`
 * 5. Configure KMAC IP in KMAC-256 mode via `kmac_kmac256_sw_configure()`.
 * 6. Load software key via `kmac_kmac256_sw_key((const uint32_t *)kdk, 8)`.
 * 7. Set customization prefix (label): `kmac_kmac256_set_prefix("My Tagged
 * Application", 21)`.
 * 8. Absorb context via `kmac_kmac256_absorb(context, 4)`.
 * 9. Squeeze 16 words (64 bytes) via `kmac_kmac256_final(digest_words, 16)`.
 * 10. Compare computed output against `expected_km`.
 */
typedef struct fips_kat_kdf_kmac256 {
  uint32_t key_len;
  uint32_t msg_len;
  uint32_t digest_len;
  uint8_t data[100];
} fips_kat_kdf_kmac256_t;

/**
 * Algorithm 17: RSA-4096 PKCS#1 v1.5 Signing (Alg ID 17)
 *
 * Source Standard: FIPS 186-4 (Section 5) / PKCS #1 v1.5 / CAVP Vector.
 *
 * Test Vector Parameters:
 * - Private Key Modulus N: 512 bytes (4096-bit).
 * - Private Exponent D: 512 bytes (4096-bit).
 * - Message: 13 bytes ("Test message.").
 * - Hash Function: SHA2-512.
 * - Expected Signature S: 512 bytes (4096-bit).
 *
 * How inputs/outputs were transformed:
 * - Header Fields:
 *     priv_key_len  = 1024 (512-byte modulus N || 512-byte private exponent D)
 *     ephemeral_len = 0
 *     msg_len       = 13   (13-byte ASCII message "Test message.")
 *     sig_len1      = 512  (512-byte / 4096-bit expected signature S)
 *     sig_len2      = 0
 * - Contiguous Payload:
 *     data[0..511]     = 512-byte modulus N (little-endian word serialized)
 *     data[512..1023]  = 512-byte private exponent D (little-endian word
 * serialized) data[1024..1036] = 13-byte message "Test message."
 *     data[1037..1039] = 3 bytes 0x00 padding for 4-byte Ibex alignment
 *     data[1040..1551] = 512-byte signature S (little-endian word serialized)
 * - Ibex Alignment: 20 bytes (header: 5 x uint32_t) + 1552 bytes (payload)
 *   = 1572 bytes total (`1572 % 4 == 0`). Naturally 4-byte aligned.
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgRsa4096Sign`.
 * 2. Dereference as `const asymmetric_sign_kat_data_t *kat =
 * get_fips_data(table, entry)`.
 * 3. Verify parameters: `kat->priv_key_len == 1024`, `kat->ephemeral_len == 0`,
 * `kat->msg_len == 13`, `kat->sig_len1 == 512`.
 * 4. Extract pointers:
 *      `const uint32_t *modulus = (const uint32_t *)kat->data;`
 *      `const uint32_t *d_share0 = (const uint32_t *)(kat->data + 512);`
 *      `const uint8_t *msg = kat->data + kat->priv_key_len;`
 *      `const uint32_t *expected_sig = (const uint32_t *)(kat->data +
 * kat->priv_key_len + ((kat->msg_len + 3) & ~3u));`
 * 5. Construct private key using
 * `otcrypto_rsa_private_key_from_exponents(kOtcryptoRsaSize4096, &modulus,
 * &d_share0, &d_share1, &private_key)`.
 * 6. Compute SHA2-512 digest of `msg` using `otcrypto_sha2_512()`.
 * 7. Execute RSA-4096 PKCS#1 v1.5 signature generation using OTBN coprocessor
 * via `otcrypto_rsa_sign()`.
 * 8. Assert generated signature equals `expected_sig`.
 */
typedef struct fips_kat_rsa_4096_sign {
  uint32_t priv_key_len;
  uint32_t ephemeral_len;
  uint32_t msg_len;
  uint32_t sig_len1;
  uint32_t sig_len2;
  uint8_t data[1552];
} fips_kat_rsa_4096_sign_t;

/**
 * Algorithm 18: RSA-4096 PKCS#1 v1.5 Verification (Alg ID 18)
 *
 * Source Standard: FIPS 186-4 (Section 5) / PKCS #1 v1.5 / CAVP Vector.
 *
 * Test Vector Parameters:
 * - Public Key Modulus N: 512 bytes (4096-bit).
 * - Public Exponent e: 4 bytes (32-bit: 65537 / 0x00010001).
 * - Message: 13 bytes ("Test message.").
 * - Hash Function: SHA2-512.
 * - Signature S: 512 bytes (4096-bit).
 *
 * How inputs/outputs were transformed:
 * - Header Fields:
 *     pub_key_len1 = 512 (512-byte / 4096-bit modulus N)
 *     pub_key_len2 = 4   (4-byte public exponent e = 65537)
 *     msg_len      = 13  (13-byte ASCII message "Test message.")
 *     sig_len1     = 512 (512-byte / 4096-bit expected signature S)
 *     sig_len2     = 0
 * - Contiguous Payload:
 *     data[0..511]     = 512-byte modulus N (little-endian word serialized)
 *     data[512..515]   = 4-byte public exponent e (0x01, 0x00, 0x01, 0x00)
 *     data[516..528]   = 13-byte message "Test message."
 *     data[529..531]   = 3 bytes 0x00 padding for 4-byte Ibex alignment
 *     data[532..1043]  = 512-byte signature S (little-endian word serialized)
 * - Ibex Alignment: 20 bytes (header: 5 x uint32_t) + 1044 bytes (payload)
 *   = 1064 bytes total (`1064 % 4 == 0`). Naturally 4-byte aligned.
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgRsa4096Verify`.
 * 2. Dereference as `const asymmetric_verify_kat_data_t *kat =
 * get_fips_data(table, entry)`.
 * 3. Verify parameters: `kat->pub_key_len1 == 512`, `kat->pub_key_len2 == 4`,
 * `kat->msg_len == 13`, `kat->sig_len1 == 512`.
 * 4. Extract pointers:
 *      `const uint32_t *modulus = (const uint32_t *)kat->data;`
 *      `const uint8_t *msg = kat->data + kat->pub_key_len1 +
 * kat->pub_key_len2;` `const uint32_t *sig = (const uint32_t *)(kat->data +
 * kat->pub_key_len1 + kat->pub_key_len2 + ((kat->msg_len + 3) & ~3u));`
 * 5. Construct public key using
 * `otcrypto_rsa_public_key_construct(kOtcryptoRsaSize4096, &mod_buf,
 * &public_key)`.
 * 6. Compute SHA2-512 digest of `msg` using `otcrypto_sha2_512()`.
 * 7. Execute RSA-4096 PKCS#1 v1.5 verification using OTBN coprocessor via
 * `otcrypto_rsa_verify()`.
 * 8. Assert verification result is `kHardenedBoolTrue`.
 */
typedef struct fips_kat_rsa_4096_verify {
  uint32_t pub_key_len1;
  uint32_t pub_key_len2;
  uint32_t msg_len;
  uint32_t sig_len1;
  uint32_t sig_len2;
  uint8_t data[1044];
} fips_kat_rsa_4096_verify_t;

/**
 * Algorithm 19: ECDSA-P256 Signature Generation (Alg ID 19)
 *
 * Source Standard: FIPS 186-4 (Section 6) / NIST CAVP ECDSA Vector (P-256,
 * SHA-256).
 *
 * Test Vector Parameters:
 * - Private Key Scalar d: 32 bytes (256-bit).
 * - Ephemeral Secret Scalar k: 32 bytes (256-bit).
 * - Message Digest: 32 bytes (SHA2-256 pre-hashed).
 * - Expected Signature: r (32 bytes), s (32 bytes).
 *
 * How inputs/outputs were transformed:
 * - Header Fields:
 *     priv_key_len  = 32 (32-byte private key scalar d)
 *     ephemeral_len = 32 (32-byte secret scalar k)
 *     msg_len       = 32 (32-byte pre-hashed message digest)
 *     sig_len1      = 32 (32-byte signature component r)
 *     sig_len2      = 32 (32-byte signature component s)
 * - Contiguous Payload:
 *     data[0..31]    = 32-byte private key scalar d (little-endian serialized)
 *     data[32..63]   = 32-byte ephemeral secret scalar k (little-endian
 * serialized) data[64..95]   = 32-byte message digest data[96..127]  = 32-byte
 * expected signature component r (little-endian serialized) data[128..159] =
 * 32-byte expected signature component s (little-endian serialized)
 * - Ibex Alignment: 20 bytes (header: 5 x uint32_t) + 160 bytes (payload)
 *   = 180 bytes total (`180 % 4 == 0`). Naturally 4-byte aligned.
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgEcdsaP256Sign`.
 * 2. Dereference as `const asymmetric_sign_kat_data_t *kat =
 * get_fips_data(table, entry)`.
 * 3. Verify parameters: `kat->priv_key_len == 32`, `kat->ephemeral_len == 32`,
 * `kat->msg_len == 32`, `kat->sig_len1 == 32`, `kat->sig_len2 == 32`.
 * 4. Extract pointers:
 *      `const uint8_t *d = kat->data;`
 *      `const uint8_t *k = kat->data + kat->priv_key_len;`
 *      `const uint8_t *msg_digest = kat->data + kat->priv_key_len +
 * kat->ephemeral_len;` `const uint8_t *expected_sig = kat->data +
 * kat->priv_key_len + kat->ephemeral_len + kat->msg_len;`
 * 5. Construct blinded private key and secret scalar using `kP256Config`.
 * 6. Execute deterministic ECDSA-P256 signing with secret scalar k using OTBN
 * coprocessor via `otcrypto_ecdsa_p256_sign_config_k()`.
 * 7. Assert generated signature (r || s) equals `expected_sig`.
 */
typedef struct fips_kat_ecdsa_p256_sign {
  uint32_t priv_key_len;
  uint32_t ephemeral_len;
  uint32_t msg_len;
  uint32_t sig_len1;
  uint32_t sig_len2;
  uint8_t data[160];
} fips_kat_ecdsa_p256_sign_t;

/**
 * Algorithm 20: ECDSA-P256 Signature Verification (Alg ID 20)
 *
 * Source Standard: FIPS 186-4 (Section 6) / NIST CAVP ECDSA Vector (P-256,
 * SHA-256).
 *
 * Test Vector Parameters:
 * - Public Key Coordinate Qx: 32 bytes (256-bit).
 * - Public Key Coordinate Qy: 32 bytes (256-bit).
 * - Message Digest: 32 bytes (SHA2-256 pre-hashed).
 * - Signature: r (32 bytes), s (32 bytes).
 *
 * How inputs/outputs were transformed:
 * - Header Fields:
 *     pub_key_len1 = 32 (32-byte public key coordinate Qx)
 *     pub_key_len2 = 32 (32-byte public key coordinate Qy)
 *     msg_len      = 32 (32-byte pre-hashed message digest)
 *     sig_len1     = 32 (32-byte signature component r)
 *     sig_len2     = 32 (32-byte signature component s)
 * - Contiguous Payload:
 *     data[0..31]    = 32-byte public key coordinate Qx (little-endian
 * serialized) data[32..63]   = 32-byte public key coordinate Qy (little-endian
 * serialized) data[64..95]   = 32-byte message digest data[96..127]  = 32-byte
 * signature component r (little-endian serialized) data[128..159] = 32-byte
 * signature component s (little-endian serialized)
 * - Ibex Alignment: 20 bytes (header: 5 x uint32_t) + 160 bytes (payload)
 *   = 180 bytes total (`180 % 4 == 0`). Naturally 4-byte aligned.
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgEcdsaP256Verify`.
 * 2. Dereference as `const asymmetric_verify_kat_data_t *kat =
 * get_fips_data(table, entry)`.
 * 3. Verify parameters: `kat->pub_key_len1 == 32`, `kat->pub_key_len2 == 32`,
 * `kat->msg_len == 32`, `kat->sig_len1 == 32`, `kat->sig_len2 == 32`.
 * 4. Extract pointers:
 *      `const uint8_t *public_key_raw = kat->data;`
 *      `const uint8_t *msg_digest = kat->data + kat->pub_key_len1 +
 * kat->pub_key_len2;` `const uint8_t *sig_raw = kat->data + kat->pub_key_len1 +
 * kat->pub_key_len2 + kat->msg_len;`
 * 5. Construct unblinded public key `otcrypto_unblinded_key_t` (key_length =
 * 64).
 * 6. Execute ECDSA-P256 verification using OTBN coprocessor via
 * `otcrypto_ecdsa_p256_verify()`.
 * 7. Assert verification result is `kHardenedBoolTrue`.
 */
typedef struct fips_kat_ecdsa_p256_verify {
  uint32_t pub_key_len1;
  uint32_t pub_key_len2;
  uint32_t msg_len;
  uint32_t sig_len1;
  uint32_t sig_len2;
  uint8_t data[160];
} fips_kat_ecdsa_p256_verify_t;

/**
 * Algorithm 21: ECDSA-P384 Signature Generation (Alg ID 21)
 *
 * Source Standard: FIPS 186-4 (Section 6) / NIST CAVP ECDSA Vector (P-384,
 * SHA-384).
 *
 * Test Vector Parameters:
 * - Private Key Scalar d: 48 bytes (384-bit).
 * - Ephemeral Secret Scalar k: 48 bytes (384-bit).
 * - Message Digest: 48 bytes (SHA2-384 pre-hashed).
 * - Expected Signature: r (48 bytes), s (48 bytes).
 *
 * How inputs/outputs were transformed:
 * - Header Fields:
 *     priv_key_len  = 48 (48-byte private key scalar d)
 *     ephemeral_len = 48 (48-byte secret scalar k)
 *     msg_len       = 48 (48-byte pre-hashed message digest)
 *     sig_len1      = 48 (48-byte signature component r)
 *     sig_len2      = 48 (48-byte signature component s)
 * - Contiguous Payload:
 *     data[0..47]    = 48-byte private key scalar d (little-endian serialized)
 *     data[48..95]   = 48-byte ephemeral secret scalar k (little-endian
 * serialized) data[96..143]  = 48-byte message digest data[144..191] = 48-byte
 * expected signature component r (little-endian serialized) data[192..239] =
 * 48-byte expected signature component s (little-endian serialized)
 * - Ibex Alignment: 20 bytes (header: 5 x uint32_t) + 240 bytes (payload)
 *   = 260 bytes total (`260 % 4 == 0`). Naturally 4-byte aligned.
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgEcdsaP384Sign`.
 * 2. Dereference as `const asymmetric_sign_kat_data_t *kat =
 * get_fips_data(table, entry)`.
 * 3. Verify parameters: `kat->priv_key_len == 48`, `kat->ephemeral_len == 48`,
 * `kat->msg_len == 48`, `kat->sig_len1 == 48`, `kat->sig_len2 == 48`.
 * 4. Extract pointers:
 *      `const uint8_t *d = kat->data;`
 *      `const uint8_t *k = kat->data + kat->priv_key_len;`
 *      `const uint8_t *msg_digest = kat->data + kat->priv_key_len +
 * kat->ephemeral_len;` `const uint8_t *expected_sig = kat->data +
 * kat->priv_key_len + kat->ephemeral_len + kat->msg_len;`
 * 5. Construct blinded private key and secret scalar using `kP384Config`.
 * 6. Execute deterministic ECDSA-P384 signing with secret scalar k using OTBN
 * coprocessor via `otcrypto_ecdsa_p384_sign_config_k()`.
 * 7. Assert generated signature (r || s) equals `expected_sig`.
 */
typedef struct fips_kat_ecdsa_p384_sign {
  uint32_t priv_key_len;
  uint32_t ephemeral_len;
  uint32_t msg_len;
  uint32_t sig_len1;
  uint32_t sig_len2;
  uint8_t data[240];
} fips_kat_ecdsa_p384_sign_t;

/**
 * Algorithm 22: ECDSA-P384 Signature Verification (Alg ID 22)
 *
 * Source Standard: FIPS 186-4 (Section 6) / NIST CAVP ECDSA Vector (P-384,
 * SHA-384).
 *
 * Test Vector Parameters:
 * - Public Key Coordinate Qx: 48 bytes (384-bit).
 * - Public Key Coordinate Qy: 48 bytes (384-bit).
 * - Message Digest: 48 bytes (SHA2-384 pre-hashed).
 * - Signature: r (48 bytes), s (48 bytes).
 *
 * How inputs/outputs were transformed:
 * - Header Fields:
 *     pub_key_len1 = 48 (48-byte public key coordinate Qx)
 *     pub_key_len2 = 48 (48-byte public key coordinate Qy)
 *     msg_len      = 48 (48-byte pre-hashed message digest)
 *     sig_len1     = 48 (48-byte signature component r)
 *     sig_len2     = 48 (48-byte signature component s)
 * - Contiguous Payload:
 *     data[0..47]    = 48-byte public key coordinate Qx (little-endian
 * serialized) data[48..95]   = 48-byte public key coordinate Qy (little-endian
 * serialized) data[96..143]  = 48-byte message digest data[144..191] = 48-byte
 * signature component r (little-endian serialized) data[192..239] = 48-byte
 * signature component s (little-endian serialized)
 * - Ibex Alignment: 20 bytes (header: 5 x uint32_t) + 240 bytes (payload)
 *   = 260 bytes total (`260 % 4 == 0`). Naturally 4-byte aligned.
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgEcdsaP384Verify`.
 * 2. Dereference as `const asymmetric_verify_kat_data_t *kat =
 * get_fips_data(table, entry)`.
 * 3. Verify parameters: `kat->pub_key_len1 == 48`, `kat->pub_key_len2 == 48`,
 * `kat->msg_len == 48`, `kat->sig_len1 == 48`, `kat->sig_len2 == 48`.
 * 4. Extract pointers:
 *      `const uint8_t *public_key_raw = kat->data;`
 *      `const uint8_t *msg_digest = kat->data + kat->pub_key_len1 +
 * kat->pub_key_len2;` `const uint8_t *sig_raw = kat->data + kat->pub_key_len1 +
 * kat->pub_key_len2 + kat->msg_len;`
 * 5. Construct unblinded public key `otcrypto_unblinded_key_t` (key_length =
 * 96).
 * 6. Execute ECDSA-P384 verification using OTBN coprocessor via
 * `otcrypto_ecdsa_p384_verify()`.
 * 7. Assert verification result is `kHardenedBoolTrue`.
 */
typedef struct fips_kat_ecdsa_p384_verify {
  uint32_t pub_key_len1;
  uint32_t pub_key_len2;
  uint32_t msg_len;
  uint32_t sig_len1;
  uint32_t sig_len2;
  uint8_t data[240];
} fips_kat_ecdsa_p384_verify_t;

/**
 * Algorithm 23: Ed25519 PureEdDSA Signature Generation (Alg ID 23)
 *
 * Source Standard: RFC 8032 Section 7.1 (Test 2) / FIPS 186-5 Section 7 / NIST
 * CAVP.
 *
 * Test Vector Parameters:
 * - Private Key Seed (sk): 32 bytes (256-bit:
 * 9b08cd4cda96ff2846c3b69d0f4e11ec9f318a5b24a6ab35edf68cdafba6b84f).
 * - Ephemeral Secret Scalar: None (0 bytes, Ed25519 generates ephemeral k
 * deterministically via SHA-512).
 * - Message: 1 byte (0x72).
 * - Expected Signature: R (32 bytes), S (32 bytes).
 *
 * How inputs/outputs were transformed:
 * - Header Fields:
 *     priv_key_len  = 32 (32-byte private key seed)
 *     ephemeral_len = 0  (Ed25519 deterministic nonce derivation)
 *     msg_len       = 1  (1-byte input message)
 *     sig_len1      = 32 (32-byte signature component R)
 *     sig_len2      = 32 (32-byte signature component S)
 * - Contiguous Payload:
 *     data[0..31]   = 32-byte private key seed
 *     data[32]      = 1-byte message (0x72)
 *     data[33..35]  = 3 bytes 0x00 padding for 4-byte Ibex natural alignment
 *     data[36..67]  = 32-byte signature component R
 *     data[68..99]  = 32-byte signature component S
 * - Ibex Alignment: 20 bytes (header: 5 x uint32_t) + 100 bytes (payload)
 *   = 120 bytes total (`120 % 4 == 0`). Naturally 4-byte aligned.
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgEd25519Sign`.
 * 2. Dereference as `const asymmetric_sign_kat_data_t *kat =
 * get_fips_data(table, entry)`.
 * 3. Verify parameters: `kat->priv_key_len == 32`, `kat->ephemeral_len == 0`,
 * `kat->msg_len == 1`, `kat->sig_len1 == 32`, `kat->sig_len2 == 32`.
 * 4. Extract pointers:
 *      `const uint8_t *sk = kat->data;`
 *      `const uint8_t *msg = kat->data + kat->priv_key_len;`
 *      `const uint8_t *expected_sig = kat->data + kat->priv_key_len +
 * ((kat->msg_len + 3) & ~3u);`
 * 5. Construct blinded private key with `kEd25519Config`.
 * 6. Execute Ed25519 PureEdDSA signing using OTBN coprocessor via
 * `otcrypto_ed25519_sign()`.
 * 7. Assert generated signature (R || S) equals `expected_sig`.
 */
typedef struct fips_kat_ed25519_sign {
  uint32_t priv_key_len;
  uint32_t ephemeral_len;
  uint32_t msg_len;
  uint32_t sig_len1;
  uint32_t sig_len2;
  uint8_t data[100];
} fips_kat_ed25519_sign_t;

/**
 * Algorithm 24: Ed25519 PureEdDSA Signature Verification (Alg ID 24)
 *
 * Source Standard: RFC 8032 Section 7.1 (Test 2) / FIPS 186-5 Section 7 / NIST
 * CAVP.
 *
 * Test Vector Parameters:
 * - Public Key (pk): 32 bytes (256-bit compressed Edwards point).
 * - Message: 1 byte (0x72).
 * - Signature: R (32 bytes), S (32 bytes).
 *
 * How inputs/outputs were transformed:
 * - Header Fields:
 *     pub_key_len1 = 32 (32-byte public key)
 *     pub_key_len2 = 0  (Ed25519 uses 32-byte compressed public key)
 *     msg_len      = 1  (1-byte input message)
 *     sig_len1     = 32 (32-byte signature component R)
 *     sig_len2     = 32 (32-byte signature component S)
 * - Contiguous Payload:
 *     data[0..31]  = 32-byte public key (little-endian serialized)
 *     data[32]     = 1-byte message (0x72)
 *     data[33..35] = 3 bytes 0x00 padding for 4-byte Ibex natural alignment
 *     data[36..67] = 32-byte signature component R (little-endian serialized)
 *     data[68..99] = 32-byte signature component S (little-endian serialized)
 * - Ibex Alignment: 20 bytes (header: 5 x uint32_t) + 100 bytes (payload)
 *   = 120 bytes total (`120 % 4 == 0`). Naturally 4-byte aligned.
 *
 * How test runners (BL0 / Cryptolib) use this vector:
 * 1. Read entry offset from `fips_kat_descriptor_table_t` for
 * `kFipsKatAlgEd25519Verify`.
 * 2. Dereference as `const asymmetric_verify_kat_data_t *kat =
 * get_fips_data(table, entry)`.
 * 3. Verify parameters: `kat->pub_key_len1 == 32`, `kat->pub_key_len2 == 0`,
 * `kat->msg_len == 1`, `kat->sig_len1 == 32`, `kat->sig_len2 == 32`.
 * 4. Extract pointers:
 *      `const uint8_t *pk = kat->data;`
 *      `const uint8_t *msg = kat->data + kat->pub_key_len1;`
 *      `const uint8_t *sig_raw = kat->data + kat->pub_key_len1 + ((kat->msg_len
 * + 3) & ~3u);`
 * 5. Construct unblinded public key `otcrypto_unblinded_key_t` (key_mode =
 * kOtcryptoKeyModeEd25519, key_length = 32).
 * 6. Execute Ed25519 verification using OTBN coprocessor via
 * `otcrypto_ed25519_verify()`.
 * 7. Assert verification result is `kHardenedBoolTrue`.
 */
typedef struct fips_kat_ed25519_verify {
  uint32_t pub_key_len1;
  uint32_t pub_key_len2;
  uint32_t msg_len;
  uint32_t sig_len1;
  uint32_t sig_len2;
  uint8_t data[100];
} fips_kat_ed25519_verify_t;

/**
 * Container holding all embedded FIPS KAT vector payloads in `.fips_kat.data`.
 */
typedef struct fips_kat_data_store {
  fips_kat_sha256_pilot_t sha256_pilot;
  fips_kat_hmac_sha256_t hmac_sha256;
  fips_kat_sha512_t sha512;
  fips_kat_hmac_sha512_t hmac_sha512;
  fips_kat_shake256_t shake256;
  fips_kat_kmac256_t kmac256;
  fips_kat_aes_ecb256_t aes_ecb256;
  fips_kat_aes_cbc256_t aes_cbc256;
  fips_kat_aes_kwp256_t aes_kwp256;
  fips_kat_kdf_hmac_sha256_t kdf_hmac_sha256;
  fips_kat_kdf_kmac256_t kdf_kmac256;
  fips_kat_rsa_4096_sign_t rsa_4096_sign;
  fips_kat_rsa_4096_verify_t rsa_4096_verify;
  fips_kat_ecdsa_p256_sign_t ecdsa_p256_sign;
  fips_kat_ecdsa_p256_verify_t ecdsa_p256_verify;
  fips_kat_ecdsa_p384_sign_t ecdsa_p384_sign;
  fips_kat_ecdsa_p384_verify_t ecdsa_p384_verify;
  fips_kat_ed25519_sign_t ed25519_sign;
  fips_kat_ed25519_verify_t ed25519_verify;
} fips_kat_data_store_t;

/**
 * FIPS KAT vector data payload placed in `.fips_kat.data`.
 */
OT_SECTION(".fips_kat.data")
OT_USED
alignas(uint32_t) static const fips_kat_data_store_t kFipsKatDataStore = {
    .sha256_pilot = {
        .key_len = 0,
        .msg_len = 3,
        .digest_len = 32,
        .data = {
            'a', 'b', 'c',
            0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
            0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
            0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
            0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
        },
        .padding = {0},
    }
,
    .hmac_sha256 = {
        .key_len = 32,
        .msg_len = 50,
        .digest_len = 32,
        .data = {
            // Key (32 bytes of 0xaa)
            0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
            0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
            0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
            0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
            // Message (50 bytes of 0xdd)
            0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
            0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
            0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
            0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
            0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
            0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
            0xdd, 0xdd,
            // Expected Digest (32 bytes)
            0xcd, 0xcb, 0x12, 0x20, 0xd1, 0xec, 0xcc, 0xea,
            0x91, 0xe5, 0x3a, 0xba, 0x30, 0x92, 0xf9, 0x62,
            0xe5, 0x49, 0xfe, 0x6c, 0xe9, 0xed, 0x7f, 0xdc,
            0x43, 0x19, 0x1f, 0xbd, 0xe4, 0x5c, 0x30, 0xb0,
        },
        .padding = {0, 0},
    }
,
    .sha512 = {
        .key_len = 0,
        .msg_len = 3,
        .digest_len = 64,
        .data = {
            'a', 'b', 'c',
            // Expected Digest (64 bytes)
            0xdd, 0xaf, 0x35, 0xa1, 0x93, 0x61, 0x7a, 0xba,
            0xcc, 0x41, 0x73, 0x49, 0xae, 0x20, 0x41, 0x31,
            0x12, 0xe6, 0xfa, 0x4e, 0x89, 0xa9, 0x7e, 0xa2,
            0x0a, 0x9e, 0xee, 0xe6, 0x4b, 0x55, 0xd3, 0x9a,
            0x21, 0x92, 0x99, 0x2a, 0x27, 0x4f, 0xc1, 0xa8,
            0x36, 0xba, 0x3c, 0x23, 0xa3, 0xfe, 0xeb, 0xbd,
            0x45, 0x4d, 0x44, 0x23, 0x64, 0x3c, 0xe8, 0x0e,
            0x2a, 0x9a, 0xc9, 0x4f, 0xa5, 0x4c, 0xa4, 0x9f,
        },
        .padding = {0},
    }
,
    .hmac_sha512 = {
        .key_len = 20,
        .msg_len = 50,
        .digest_len = 64,
        .data = {
            // Key (20 bytes of 0xaa)
            0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
            0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
            0xaa, 0xaa, 0xaa, 0xaa,
            // Message (50 bytes of 0xdd)
            0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
            0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
            0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
            0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
            0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
            0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd, 0xdd,
            0xdd, 0xdd,
            // Expected Digest (64 bytes)
            0xfa, 0x73, 0xb0, 0x08, 0x9d, 0x56, 0xa2, 0x84,
            0xef, 0xb0, 0xf0, 0x75, 0x6c, 0x89, 0x0b, 0xe9,
            0xb1, 0xb5, 0xdb, 0xdd, 0x8e, 0xe8, 0x1a, 0x36,
            0x55, 0xf8, 0x3e, 0x33, 0xb2, 0x27, 0x9d, 0x39,
            0xbf, 0x3e, 0x84, 0x82, 0x79, 0xa7, 0x22, 0xc8,
            0x06, 0xb4, 0x85, 0xa4, 0x7e, 0x67, 0xc8, 0x07,
            0xb9, 0x46, 0xa3, 0x37, 0xbe, 0xe8, 0x94, 0x26,
            0x74, 0x27, 0x88, 0x59, 0xe1, 0x32, 0x92, 0xfb,
        },
        .padding = {0, 0},
    }
,
    .shake256 = {
        .key_len = 0,
        .msg_len = 1,
        .digest_len = 32,
        .data = {
            // Message (1 byte): 0x0f, followed by 3 bytes 0x00 padding for 4B word alignment
            0x0f, 0x00, 0x00, 0x00,
            // Expected Squeezed Output (32 bytes = 256 bits)
            0xaa, 0xbb, 0x07, 0x48, 0x8f, 0xf9, 0xed, 0xd0,
            0x5d, 0x6a, 0x60, 0x3b, 0x77, 0x91, 0xb6, 0x0a,
            0x16, 0xd4, 0x50, 0x93, 0x60, 0x8f, 0x1b, 0xad,
            0xc0, 0xc9, 0xcc, 0x9a, 0x91, 0x54, 0xf2, 0x15,
        },
    }
,
    .kmac256 = {
        .key_len = 32,
        .msg_len = 4,
        .digest_len = 64,
        .data = {
            // Key (32 bytes: 0x40..0x5f)
            0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47,
            0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f,
            0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57,
            0x58, 0x59, 0x5a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f,
            // Message (4 bytes: 0x00, 0x01, 0x02, 0x03)
            0x00, 0x01, 0x02, 0x03,
            // Expected Output (64 bytes = 512 bits)
            0x20, 0xc5, 0x70, 0xc3, 0x13, 0x46, 0xf7, 0x03,
            0xc9, 0xac, 0x36, 0xc6, 0x1c, 0x03, 0xcb, 0x64,
            0xc3, 0x97, 0x0d, 0x0c, 0xfc, 0x78, 0x7e, 0x9b,
            0x79, 0x59, 0x9d, 0x27, 0x3a, 0x68, 0xd2, 0xf7,
            0xf6, 0x9d, 0x4c, 0xc3, 0xde, 0x9d, 0x10, 0x4a,
            0x35, 0x16, 0x89, 0xf2, 0x7c, 0xf6, 0xf5, 0x95,
            0x1f, 0x01, 0x03, 0xf3, 0x3f, 0x4f, 0x24, 0x87,
            0x10, 0x24, 0xd9, 0xc2, 0x77, 0x73, 0xa8, 0xdd,
        },
    }
,
    .aes_ecb256 = {
        .key_len = 32,
        .iv_len = 0,
        .aad_len = 0,
        .pt_len = 16,
        .ct_len = 16,
        .tag_len = 0,
        .data = {
            // Key (32 bytes): NIST SP 800-38A Section F.1.5
            0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe,
            0x2b, 0x73, 0xae, 0xf0, 0x85, 0x7d, 0x77, 0x81,
            0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7,
            0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4,
            // Plaintext (16 bytes)
            0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
            0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
            // Ciphertext (16 bytes)
            0xf3, 0xee, 0xd1, 0xbd, 0xb5, 0xd2, 0xa0, 0x3c,
            0x06, 0x4b, 0x5a, 0x7e, 0x3d, 0xb1, 0x81, 0xf8,
        },
    }
,
    .aes_cbc256 = {
        .key_len = 32,
        .iv_len = 16,
        .aad_len = 0,
        .pt_len = 16,
        .ct_len = 16,
        .tag_len = 0,
        .data = {
            // Key (32 bytes): NIST SP 800-38A Section F.2.5
            0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe,
            0x2b, 0x73, 0xae, 0xf0, 0x85, 0x7d, 0x77, 0x81,
            0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7,
            0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4,
            // IV (16 bytes)
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
            // Plaintext (16 bytes)
            0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
            0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
            // Ciphertext (16 bytes)
            0xf5, 0x8c, 0x4c, 0x04, 0xd6, 0xe5, 0xf1, 0xba,
            0x77, 0x9e, 0xab, 0xfb, 0x5f, 0x7b, 0xfb, 0xd6,
        },
    }
,
    .aes_kwp256 = {
        .key_len = 32,
        .iv_len = 0,
        .aad_len = 0,
        .pt_len = 16,
        .ct_len = 24,
        .tag_len = 0,
        .data = {
            // Key (32 bytes)
            0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe,
            0x2b, 0x73, 0xae, 0xf0, 0x85, 0x7d, 0x77, 0x81,
            0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7,
            0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4,
            // Plaintext (16 bytes)
            0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
            0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
            // Expected Wrapped Ciphertext (24 bytes)
            0xcc, 0x06, 0xca, 0x9e, 0xd0, 0x8d, 0xb0, 0x32,
            0x13, 0x48, 0x1e, 0x0b, 0x44, 0x0d, 0x7f, 0xab,
            0xf8, 0x85, 0x0c, 0xcc, 0xad, 0x63, 0x00, 0x53,
        },
    }
,
    .kdf_hmac_sha256 = {
        .key_len = 32,
        .msg_len = 21,
        .digest_len = 32,
        .data = {
            // KDK (32 bytes of 0x0b)
            0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
            0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
            0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
            0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
            // Formatted Message (21 bytes: [i]_2 || Label || 0x00 || Context || [L]_2)
            0x00, 0x00, 0x00, 0x01,
            0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5,
            0x00,
            0x60, 0x61, 0x62, 0x63, 0x64, 0x65,
            0x00, 0x00, 0x01, 0x00,
            // 3 bytes 0x00 padding for 4B Ibex alignment
            0x00, 0x00, 0x00,
            // Expected Derived Keying Material (32 bytes)
            0x12, 0xb4, 0x4b, 0x70, 0x02, 0x76, 0xc0, 0x30,
            0x74, 0xcd, 0x99, 0xf9, 0x87, 0x63, 0x57, 0x4b,
            0x7b, 0xf7, 0x1c, 0x30, 0x34, 0x02, 0x23, 0x79,
            0x0b, 0xf0, 0xb8, 0xf5, 0x3f, 0xcf, 0x3c, 0x86,
        },
    }
,
    .kdf_kmac256 = {
        .key_len = 32,
        .msg_len = 4,
        .digest_len = 64,
        .data = {
            // KDK (32 bytes: 0x40..0x5f)
            0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47,
            0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f,
            0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57,
            0x58, 0x59, 0x5a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f,
            // Context / Message (4 bytes: 0x00, 0x01, 0x02, 0x03)
            0x00, 0x01, 0x02, 0x03,
            // Expected Output (64 bytes = 512 bits)
            0x20, 0xc5, 0x70, 0xc3, 0x13, 0x46, 0xf7, 0x03,
            0xc9, 0xac, 0x36, 0xc6, 0x1c, 0x03, 0xcb, 0x64,
            0xc3, 0x97, 0x0d, 0x0c, 0xfc, 0x78, 0x7e, 0x9b,
            0x79, 0x59, 0x9d, 0x27, 0x3a, 0x68, 0xd2, 0xf7,
            0xf6, 0x9d, 0x4c, 0xc3, 0xde, 0x9d, 0x10, 0x4a,
            0x35, 0x16, 0x89, 0xf2, 0x7c, 0xf6, 0xf5, 0x95,
            0x1f, 0x01, 0x03, 0xf3, 0x3f, 0x4f, 0x24, 0x87,
            0x10, 0x24, 0xd9, 0xc2, 0x77, 0x73, 0xa8, 0xdd,
        },
    },
    .rsa_4096_sign = {
        .priv_key_len = 1024,
        .ephemeral_len = 0,
        .msg_len = 13,
        .sig_len1 = 512,
        .sig_len2 = 0,
        .data = {
            // Private Key: Modulus N (512 bytes)
            0xe5, 0xef, 0x14, 0x31, 0xcf, 0xbd, 0xc4, 0x85,
            0x2c, 0xc8, 0xcd, 0x02, 0x8b, 0xfc, 0x80, 0xde,
            0x1c, 0x03, 0x50, 0xea, 0xb0, 0xee, 0x4c, 0x7c,
            0x53, 0x8f, 0x48, 0x17, 0x0b, 0xb3, 0x71, 0xf0,
            0x9c, 0xb6, 0xd4, 0xb1, 0x66, 0xd8, 0x6a, 0xa8,
            0x07, 0x17, 0x3d, 0xd3, 0xdc, 0xc3, 0x70, 0xa9,
            0x97, 0x21, 0x2b, 0xf2, 0x21, 0xeb, 0xb3, 0x2a,
            0xf2, 0x9b, 0x69, 0xf9, 0xa5, 0x3b, 0x47, 0x4f,
            0x1d, 0x36, 0x92, 0xef, 0xfb, 0x8d, 0x34, 0xcf,
            0x93, 0xae, 0xfe, 0x8d, 0x0c, 0xb4, 0xb2, 0xc7,
            0xfc, 0xc5, 0xb8, 0x4a, 0x04, 0x7c, 0x4c, 0x96,
            0x6c, 0x31, 0xfe, 0x74, 0xc4, 0x60, 0x9c, 0x3a,
            0x2f, 0xd1, 0xa0, 0xde, 0x73, 0xed, 0x3f, 0xff,
            0x5a, 0x49, 0xae, 0xf9, 0xd0, 0xc7, 0xac, 0xca,
            0x96, 0x7c, 0x56, 0x19, 0x4f, 0xd5, 0xea, 0xeb,
            0xa2, 0x09, 0xd1, 0x8a, 0x76, 0xf6, 0x72, 0xa2,
            0xb1, 0xb8, 0x98, 0x63, 0xb2, 0xe7, 0xde, 0x3c,
            0xba, 0x17, 0x57, 0x06, 0xd3, 0x05, 0xa4, 0x43,
            0x53, 0xa7, 0x76, 0xd4, 0xc5, 0xaf, 0x28, 0x54,
            0x07, 0x26, 0xc5, 0x69, 0xf1, 0xbe, 0x87, 0x0b,
            0x1a, 0xd7, 0xe0, 0x95, 0x44, 0x8d, 0x3d, 0xf6,
            0x05, 0x07, 0x71, 0xcc, 0x74, 0x79, 0x95, 0x43,
            0x5f, 0x0c, 0xc4, 0x04, 0x66, 0x87, 0x2f, 0xb0,
            0x5e, 0x19, 0x87, 0x0d, 0x24, 0x0b, 0x69, 0x4a,
            0x25, 0x25, 0x71, 0x21, 0x6b, 0x03, 0x4a, 0xbf,
            0x46, 0x3e, 0x59, 0xef, 0x60, 0xe7, 0xf8, 0x69,
            0xe5, 0x8e, 0x53, 0x1f, 0x1d, 0x54, 0x6b, 0x45,
            0x00, 0x94, 0x58, 0x9d, 0x94, 0x5b, 0xc0, 0x59,
            0xfb, 0xd7, 0x26, 0x5b, 0x03, 0x3c, 0x54, 0xb9,
            0x1e, 0x97, 0xfc, 0x78, 0x70, 0xc9, 0x14, 0xd2,
            0xa1, 0x02, 0xbf, 0x87, 0x03, 0xca, 0x05, 0xf4,
            0xf1, 0xce, 0x8a, 0x67, 0x10, 0x00, 0xad, 0x9e,
            0x74, 0x78, 0xda, 0x92, 0xa5, 0x9e, 0xae, 0x68,
            0xa1, 0x2f, 0x77, 0x5d, 0x1c, 0x4a, 0x58, 0xae,
            0x21, 0xb9, 0x41, 0xa3, 0xa6, 0x5d, 0x79, 0xf9,
            0x66, 0x71, 0x13, 0x84, 0x9a, 0x6f, 0x4c, 0xd9,
            0x3f, 0x6e, 0x36, 0xe9, 0x46, 0xfe, 0xb2, 0xf7,
            0x34, 0x65, 0x1e, 0x37, 0x5e, 0xaa, 0x16, 0x9a,
            0x13, 0x0a, 0x1a, 0x74, 0x8d, 0x93, 0x2c, 0xcf,
            0xe9, 0xdf, 0x4b, 0x16, 0x1a, 0x8e, 0x1e, 0xf4,
            0x66, 0x1c, 0xb8, 0x76, 0x38, 0x01, 0x97, 0xfb,
            0x01, 0x52, 0x60, 0xe4, 0xbc, 0xc2, 0x4b, 0x6c,
            0xca, 0x51, 0xba, 0x48, 0x98, 0x86, 0x0a, 0x91,
            0xb4, 0xae, 0xb6, 0x52, 0x71, 0xa2, 0x1b, 0x30,
            0xe4, 0x42, 0x4b, 0x7d, 0x66, 0xf3, 0x20, 0x9a,
            0x34, 0x1b, 0x6d, 0x45, 0xcf, 0xbf, 0xc2, 0x2a,
            0xec, 0x50, 0xdb, 0xa9, 0xc3, 0x94, 0x24, 0x5e,
            0x8c, 0x23, 0x83, 0xda, 0xac, 0xdd, 0x33, 0x07,
            0x11, 0x46, 0x1a, 0xc1, 0x99, 0x45, 0xf5, 0xe6,
            0xde, 0xa8, 0x80, 0xa0, 0xb7, 0x22, 0x35, 0xa8,
            0x46, 0x18, 0xf4, 0x28, 0x9e, 0xc0, 0xc7, 0xc5,
            0x08, 0x69, 0x17, 0xdf, 0x07, 0xe0, 0x97, 0x27,
            0x56, 0x10, 0xc1, 0x78, 0x68, 0xc6, 0x16, 0xe6,
            0x63, 0x47, 0xd3, 0xf7, 0x31, 0x40, 0x27, 0x94,
            0x97, 0x0d, 0x89, 0x81, 0xe6, 0x5d, 0x97, 0xb7,
            0x43, 0x4b, 0xa2, 0xca, 0x61, 0x71, 0x53, 0xee,
            0x55, 0xeb, 0x96, 0x50, 0xae, 0x41, 0x37, 0xc9,
            0x92, 0x5b, 0xb5, 0xf3, 0xb9, 0xac, 0x11, 0xa9,
            0xc8, 0xc1, 0x9e, 0xca, 0x8b, 0xd1, 0x11, 0x87,
            0x4f, 0x52, 0xff, 0xbd, 0x4a, 0x47, 0x9f, 0x14,
            0x64, 0x57, 0x45, 0xca, 0xd6, 0xf3, 0xcf, 0xf5,
            0x92, 0x01, 0xa0, 0x74, 0x1e, 0xc4, 0x56, 0xbb,
            0x78, 0x27, 0xb1, 0xb7, 0xcb, 0xec, 0x2c, 0xc5,
            0x67, 0x08, 0x10, 0xb8, 0xb1, 0x26, 0x3d, 0x92,
            // Private Key: Exponent D (512 bytes)
            0x51, 0xe6, 0x05, 0x26, 0x8d, 0x10, 0x09, 0x21,
            0xd0, 0x18, 0x0f, 0x4c, 0xbe, 0xac, 0x4c, 0xed,
            0x1d, 0xc6, 0x11, 0x6b, 0x78, 0x9c, 0xbc, 0xbd,
            0x38, 0xfb, 0xcb, 0x2f, 0xa9, 0xde, 0x77, 0xe0,
            0xf1, 0x7f, 0x97, 0x4a, 0xe0, 0x18, 0xa2, 0x90,
            0xaf, 0xc1, 0x0c, 0x01, 0xdb, 0xf5, 0x1c, 0xed,
            0xb9, 0xef, 0x86, 0x0a, 0x3a, 0xec, 0xf0, 0xf0,
            0x95, 0x67, 0x65, 0xdb, 0xd4, 0xa8, 0xbc, 0xa6,
            0xd6, 0x75, 0xc0, 0x1f, 0xca, 0x5b, 0xb9, 0xcc,
            0x3e, 0x76, 0x07, 0x17, 0xc1, 0xa4, 0x82, 0xdb,
            0xad, 0xf7, 0x55, 0x92, 0xa3, 0x9d, 0x2a, 0x25,
            0x58, 0x66, 0xc1, 0xf3, 0x36, 0x7d, 0x8f, 0x24,
            0x5e, 0x08, 0x40, 0xcf, 0x58, 0x40, 0x20, 0x01,
            0x78, 0xce, 0x48, 0xea, 0x75, 0xf8, 0x1b, 0x9d,
            0x12, 0x8a, 0x0c, 0xa4, 0x8a, 0xbd, 0xb8, 0x4e,
            0xf6, 0xf4, 0x2d, 0xe6, 0xe4, 0xbe, 0x9c, 0xf2,
            0x0e, 0x0c, 0xa1, 0xe3, 0xf1, 0xd6, 0x6e, 0x6a,
            0x50, 0x07, 0x01, 0xbd, 0xcc, 0xa3, 0x7a, 0xf8,
            0xe8, 0x5f, 0xa7, 0x1a, 0x32, 0x9c, 0x33, 0xfb,
            0xb7, 0xee, 0xf1, 0x7a, 0x46, 0x50, 0x89, 0x9e,
            0xe5, 0x46, 0x0f, 0xff, 0x68, 0x19, 0xb3, 0xee,
            0x1b, 0xab, 0x30, 0x31, 0xb9, 0x0e, 0xa0, 0xed,
            0x0f, 0x47, 0x55, 0x79, 0x8a, 0x25, 0xa8, 0xcd,
            0x5c, 0xf2, 0x09, 0x34, 0xf5, 0x75, 0x7d, 0x08,
            0x6d, 0x1f, 0x37, 0xe9, 0x98, 0x28, 0xfb, 0x73,
            0xdb, 0x6f, 0x14, 0x1b, 0xf6, 0x69, 0x72, 0x9c,
            0x26, 0x07, 0x4e, 0xbc, 0xe8, 0x9c, 0x01, 0x3a,
            0xa9, 0x11, 0xa2, 0x63, 0xc4, 0x3a, 0xd5, 0x53,
            0xa5, 0x03, 0xbc, 0x56, 0x8a, 0x41, 0x62, 0x7a,
            0xec, 0x62, 0x84, 0x00, 0xec, 0xc6, 0xed, 0x08,
            0xb7, 0x04, 0xa0, 0x9e, 0x02, 0xec, 0x7f, 0x29,
            0x8c, 0x89, 0x8a, 0x65, 0x98, 0xcf, 0xfe, 0x17,
            0x14, 0x86, 0xdf, 0xbb, 0x48, 0x2e, 0xd6, 0x35,
            0xf0, 0x33, 0x27, 0x73, 0xdd, 0x8a, 0xb6, 0xfa,
            0x69, 0x37, 0xf3, 0xd5, 0x44, 0xe5, 0xc3, 0x20,
            0xe6, 0x94, 0xb9, 0x6f, 0x54, 0x34, 0xe3, 0xd6,
            0x81, 0x74, 0xf4, 0xe5, 0xc2, 0xee, 0x1f, 0xd7,
            0x98, 0x26, 0x65, 0xfa, 0x71, 0x9a, 0x79, 0x3f,
            0xca, 0x04, 0x3a, 0x7c, 0xe6, 0x6f, 0x48, 0x30,
            0xa1, 0x12, 0x1e, 0x43, 0x8b, 0x3f, 0x60, 0x2c,
            0x99, 0x02, 0x7d, 0x5a, 0x53, 0xbd, 0xf6, 0x99,
            0xa0, 0x38, 0x4c, 0x52, 0x9e, 0x02, 0x82, 0x82,
            0xa3, 0x0f, 0x2f, 0xca, 0xd6, 0x68, 0xdc, 0xaa,
            0xf7, 0xcc, 0xee, 0x7c, 0x78, 0xbc, 0x38, 0xe1,
            0x5b, 0xf9, 0x13, 0x50, 0x4a, 0x4d, 0xc6, 0x1a,
            0x06, 0x0f, 0x28, 0xb1, 0x54, 0x51, 0xc3, 0x08,
            0xd7, 0x46, 0x5b, 0x14, 0x51, 0x4a, 0xde, 0xcb,
            0x78, 0xbb, 0x70, 0x98, 0x12, 0x1a, 0xa6, 0x47,
            0xf8, 0x7d, 0x53, 0xdd, 0x01, 0x39, 0x33, 0xd4,
            0x60, 0xf9, 0xa2, 0x13, 0xb4, 0x9c, 0xd1, 0xe4,
            0xfc, 0xe3, 0xd4, 0xc1, 0xb5, 0x50, 0x70, 0x78,
            0x7c, 0x3e, 0xa6, 0x16, 0x09, 0x73, 0x5c, 0x14,
            0xcb, 0xb6, 0x11, 0x16, 0x9e, 0x68, 0x39, 0x57,
            0xbd, 0xa8, 0xd2, 0x87, 0x5f, 0x2d, 0x44, 0xfd,
            0x4f, 0x7d, 0x97, 0x5f, 0x65, 0x11, 0x29, 0x6b,
            0xcc, 0xe9, 0xfe, 0xb5, 0xc8, 0x16, 0x06, 0x45,
            0x54, 0x7a, 0xde, 0x1e, 0x4d, 0x58, 0x45, 0x4f,
            0x75, 0x12, 0xab, 0x22, 0xa4, 0xa9, 0x47, 0x0d,
            0xab, 0xa9, 0x32, 0xd7, 0xbf, 0x5c, 0x22, 0xeb,
            0xbf, 0xc3, 0x43, 0xd0, 0x58, 0xc5, 0x73, 0xd6,
            0xad, 0x9d, 0x82, 0x71, 0xd2, 0x21, 0xc7, 0x5b,
            0x47, 0x5e, 0x37, 0x66, 0x3b, 0x3d, 0xa5, 0x63,
            0x66, 0xec, 0xd9, 0x16, 0xb6, 0xc3, 0xa2, 0x18,
            0x08, 0x94, 0x5d, 0x96, 0x83, 0xcb, 0xaa, 0x19,
            // Message (13 bytes: "Test message.")
            'T', 'e', 's', 't', ' ', 'm', 'e', 's', 's', 'a', 'g', 'e', '.',
            // Padding (3 bytes 0x00 for 4-byte Ibex alignment)
            0x00, 0x00, 0x00,
            // Expected Signature S (512 bytes)
            0xe6, 0x79, 0x15, 0x43, 0xfd, 0xc3, 0x4d, 0x4a,
            0x92, 0xee, 0x82, 0xdd, 0x2b, 0x98, 0x94, 0xee,
            0xe2, 0xf7, 0x05, 0xc0, 0x17, 0xb7, 0xe5, 0x85,
            0xf2, 0x9f, 0xc5, 0x60, 0xf2, 0xdf, 0x1d, 0x20,
            0xbe, 0x81, 0xf5, 0x96, 0xaa, 0xe3, 0x3f, 0x50,
            0x80, 0x81, 0x0f, 0xef, 0x2c, 0xf8, 0x7f, 0xb4,
            0xf8, 0x23, 0xa8, 0xc8, 0xa0, 0x8c, 0x73, 0x71,
            0x25, 0xcf, 0x3d, 0xb8, 0xc7, 0x90, 0xb9, 0x17,
            0xfa, 0xd7, 0xf1, 0xd9, 0x14, 0xba, 0xd3, 0x80,
            0x2f, 0x42, 0xff, 0x13, 0xde, 0x56, 0x6e, 0x9d,
            0xe0, 0x47, 0x2b, 0xb6, 0xbc, 0xb9, 0xf0, 0xa4,
            0x71, 0x9c, 0x0a, 0x94, 0x1c, 0x07, 0xb2, 0x69,
            0xdb, 0x4e, 0xe3, 0xdb, 0x32, 0xd9, 0x63, 0xfe,
            0x6f, 0xc1, 0xd9, 0xcc, 0x25, 0xed, 0xf4, 0x5e,
            0x46, 0x98, 0xc7, 0x1e, 0x58, 0x11, 0x21, 0x07,
            0x9d, 0x2c, 0xae, 0x8c, 0x5a, 0xef, 0xe2, 0x62,
            0xe0, 0xc4, 0x2c, 0x25, 0xda, 0xad, 0xba, 0xe8,
            0x33, 0x96, 0x42, 0xae, 0x43, 0x08, 0x9f, 0x42,
            0x00, 0x62, 0xdd, 0x40, 0xb0, 0x36, 0xc8, 0x04,
            0xdf, 0x9a, 0x40, 0x8c, 0xd1, 0xad, 0xb2, 0x73,
            0x74, 0x0a, 0xaa, 0x36, 0x9b, 0xef, 0xda, 0xfa,
            0x74, 0x1f, 0xee, 0xac, 0x0f, 0x18, 0x7b, 0x5b,
            0x40, 0x31, 0xad, 0x8f, 0xa2, 0x46, 0xc6, 0xce,
            0x5c, 0xdf, 0x8d, 0x40, 0x7f, 0xee, 0x38, 0x1d,
            0x59, 0xd4, 0x40, 0xf2, 0x5c, 0xc2, 0xdf, 0xfa,
            0xe4, 0x7e, 0x64, 0x97, 0xd5, 0x65, 0xd9, 0x42,
            0x16, 0xee, 0xf6, 0xdb, 0x35, 0xcf, 0x79, 0xc4,
            0xd3, 0x3c, 0xe3, 0x87, 0xce, 0xbf, 0x88, 0xac,
            0x6e, 0x52, 0x32, 0x6f, 0xe0, 0x1c, 0x80, 0xea,
            0x71, 0xee, 0xfe, 0x74, 0x64, 0xc4, 0xa6, 0x00,
            0xda, 0x7a, 0xb9, 0x8e, 0x2e, 0x3e, 0xb0, 0xb8,
            0x33, 0xd2, 0x43, 0x27, 0xca, 0x3b, 0x01, 0x4b,
            0x70, 0xa6, 0xe1, 0x9f, 0xc8, 0x87, 0xa9, 0x20,
            0xce, 0x1e, 0xe0, 0x0e, 0xcc, 0x17, 0xd6, 0xad,
            0xef, 0x54, 0xfa, 0xa3, 0x80, 0x7d, 0x09, 0x52,
            0xa2, 0x63, 0x95, 0x0a, 0x84, 0xfd, 0xdb, 0xb9,
            0xce, 0x35, 0x94, 0xf0, 0xe0, 0x3a, 0xeb, 0x98,
            0x20, 0xae, 0xbf, 0x51, 0x79, 0x4d, 0x8b, 0x6a,
            0xd8, 0xe7, 0x34, 0x47, 0x5c, 0x62, 0xc9, 0x0e,
            0xe2, 0x91, 0x64, 0x96, 0x9d, 0x5f, 0x3d, 0xb9,
            0x11, 0x98, 0xd3, 0x1e, 0xff, 0x1e, 0x7e, 0x81,
            0x8f, 0xa1, 0x9f, 0x50, 0xf9, 0xc2, 0x62, 0x76,
            0x86, 0x7f, 0xc8, 0x6b, 0x27, 0x00, 0x79, 0x75,
            0xad, 0xf1, 0x5a, 0xa7, 0x9e, 0x35, 0x7b, 0x3f,
            0x7a, 0x0f, 0x8b, 0x0e, 0x5d, 0xbe, 0x12, 0x28,
            0xbf, 0xb0, 0x22, 0xcf, 0xa1, 0xa9, 0xb8, 0xe8,
            0x0b, 0x27, 0xd1, 0xa4, 0x58, 0x2b, 0x0f, 0x99,
            0xfa, 0xd2, 0x04, 0xd6, 0xdd, 0x50, 0x01, 0x0c,
            0x4b, 0x3b, 0x57, 0x98, 0xfe, 0x11, 0xe9, 0x26,
            0x49, 0x6e, 0xc1, 0xc3, 0xb3, 0xd3, 0x32, 0x6e,
            0x31, 0x06, 0x19, 0x74, 0x6b, 0x40, 0x4c, 0x46,
            0x62, 0xce, 0x24, 0x81, 0xc5, 0x3e, 0x6c, 0x44,
            0x08, 0x2c, 0x5a, 0xde, 0x9b, 0x9f, 0xcf, 0xd0,
            0xca, 0x66, 0x5b, 0x1b, 0xfa, 0xe9, 0x59, 0x6e,
            0x4a, 0x72, 0x96, 0x9b, 0xe1, 0xee, 0xa5, 0x8c,
            0xa6, 0x1b, 0xa3, 0xe9, 0x85, 0x06, 0x82, 0xd7,
            0xf5, 0x7a, 0xf9, 0x77, 0x45, 0xb9, 0x0b, 0x3f,
            0x12, 0x5f, 0xe3, 0xba, 0xe8, 0x54, 0xcf, 0xd2,
            0x09, 0x89, 0xb5, 0xe0, 0x43, 0x99, 0xae, 0xa2,
            0x56, 0x34, 0xb0, 0x1e, 0x0b, 0xc4, 0xca, 0x5d,
            0xa0, 0x5f, 0xbf, 0x05, 0xc2, 0xd2, 0x45, 0xc7,
            0xfb, 0x04, 0x40, 0x62, 0x18, 0x19, 0x5c, 0x44,
            0x9d, 0x39, 0x53, 0x38, 0xe2, 0x2a, 0x8f, 0x73,
            0xa5, 0xa0, 0x1c, 0xd3, 0x53, 0x5e, 0xaf, 0x2d,
        },
    }
,
    .rsa_4096_verify = {
        .pub_key_len1 = 512,
        .pub_key_len2 = 4,
        .msg_len = 13,
        .sig_len1 = 512,
        .sig_len2 = 0,
        .data = {
            // Modulus N (512 bytes)
            0xe5, 0xef, 0x14, 0x31, 0xcf, 0xbd, 0xc4, 0x85,
            0x2c, 0xc8, 0xcd, 0x02, 0x8b, 0xfc, 0x80, 0xde,
            0x1c, 0x03, 0x50, 0xea, 0xb0, 0xee, 0x4c, 0x7c,
            0x53, 0x8f, 0x48, 0x17, 0x0b, 0xb3, 0x71, 0xf0,
            0x9c, 0xb6, 0xd4, 0xb1, 0x66, 0xd8, 0x6a, 0xa8,
            0x07, 0x17, 0x3d, 0xd3, 0xdc, 0xc3, 0x70, 0xa9,
            0x97, 0x21, 0x2b, 0xf2, 0x21, 0xeb, 0xb3, 0x2a,
            0xf2, 0x9b, 0x69, 0xf9, 0xa5, 0x3b, 0x47, 0x4f,
            0x1d, 0x36, 0x92, 0xef, 0xfb, 0x8d, 0x34, 0xcf,
            0x93, 0xae, 0xfe, 0x8d, 0x0c, 0xb4, 0xb2, 0xc7,
            0xfc, 0xc5, 0xb8, 0x4a, 0x04, 0x7c, 0x4c, 0x96,
            0x6c, 0x31, 0xfe, 0x74, 0xc4, 0x60, 0x9c, 0x3a,
            0x2f, 0xd1, 0xa0, 0xde, 0x73, 0xed, 0x3f, 0xff,
            0x5a, 0x49, 0xae, 0xf9, 0xd0, 0xc7, 0xac, 0xca,
            0x96, 0x7c, 0x56, 0x19, 0x4f, 0xd5, 0xea, 0xeb,
            0xa2, 0x09, 0xd1, 0x8a, 0x76, 0xf6, 0x72, 0xa2,
            0xb1, 0xb8, 0x98, 0x63, 0xb2, 0xe7, 0xde, 0x3c,
            0xba, 0x17, 0x57, 0x06, 0xd3, 0x05, 0xa4, 0x43,
            0x53, 0xa7, 0x76, 0xd4, 0xc5, 0xaf, 0x28, 0x54,
            0x07, 0x26, 0xc5, 0x69, 0xf1, 0xbe, 0x87, 0x0b,
            0x1a, 0xd7, 0xe0, 0x95, 0x44, 0x8d, 0x3d, 0xf6,
            0x05, 0x07, 0x71, 0xcc, 0x74, 0x79, 0x95, 0x43,
            0x5f, 0x0c, 0xc4, 0x04, 0x66, 0x87, 0x2f, 0xb0,
            0x5e, 0x19, 0x87, 0x0d, 0x24, 0x0b, 0x69, 0x4a,
            0x25, 0x25, 0x71, 0x21, 0x6b, 0x03, 0x4a, 0xbf,
            0x46, 0x3e, 0x59, 0xef, 0x60, 0xe7, 0xf8, 0x69,
            0xe5, 0x8e, 0x53, 0x1f, 0x1d, 0x54, 0x6b, 0x45,
            0x00, 0x94, 0x58, 0x9d, 0x94, 0x5b, 0xc0, 0x59,
            0xfb, 0xd7, 0x26, 0x5b, 0x03, 0x3c, 0x54, 0xb9,
            0x1e, 0x97, 0xfc, 0x78, 0x70, 0xc9, 0x14, 0xd2,
            0xa1, 0x02, 0xbf, 0x87, 0x03, 0xca, 0x05, 0xf4,
            0xf1, 0xce, 0x8a, 0x67, 0x10, 0x00, 0xad, 0x9e,
            0x74, 0x78, 0xda, 0x92, 0xa5, 0x9e, 0xae, 0x68,
            0xa1, 0x2f, 0x77, 0x5d, 0x1c, 0x4a, 0x58, 0xae,
            0x21, 0xb9, 0x41, 0xa3, 0xa6, 0x5d, 0x79, 0xf9,
            0x66, 0x71, 0x13, 0x84, 0x9a, 0x6f, 0x4c, 0xd9,
            0x3f, 0x6e, 0x36, 0xe9, 0x46, 0xfe, 0xb2, 0xf7,
            0x34, 0x65, 0x1e, 0x37, 0x5e, 0xaa, 0x16, 0x9a,
            0x13, 0x0a, 0x1a, 0x74, 0x8d, 0x93, 0x2c, 0xcf,
            0xe9, 0xdf, 0x4b, 0x16, 0x1a, 0x8e, 0x1e, 0xf4,
            0x66, 0x1c, 0xb8, 0x76, 0x38, 0x01, 0x97, 0xfb,
            0x01, 0x52, 0x60, 0xe4, 0xbc, 0xc2, 0x4b, 0x6c,
            0xca, 0x51, 0xba, 0x48, 0x98, 0x86, 0x0a, 0x91,
            0xb4, 0xae, 0xb6, 0x52, 0x71, 0xa2, 0x1b, 0x30,
            0xe4, 0x42, 0x4b, 0x7d, 0x66, 0xf3, 0x20, 0x9a,
            0x34, 0x1b, 0x6d, 0x45, 0xcf, 0xbf, 0xc2, 0x2a,
            0xec, 0x50, 0xdb, 0xa9, 0xc3, 0x94, 0x24, 0x5e,
            0x8c, 0x23, 0x83, 0xda, 0xac, 0xdd, 0x33, 0x07,
            0x11, 0x46, 0x1a, 0xc1, 0x99, 0x45, 0xf5, 0xe6,
            0xde, 0xa8, 0x80, 0xa0, 0xb7, 0x22, 0x35, 0xa8,
            0x46, 0x18, 0xf4, 0x28, 0x9e, 0xc0, 0xc7, 0xc5,
            0x08, 0x69, 0x17, 0xdf, 0x07, 0xe0, 0x97, 0x27,
            0x56, 0x10, 0xc1, 0x78, 0x68, 0xc6, 0x16, 0xe6,
            0x63, 0x47, 0xd3, 0xf7, 0x31, 0x40, 0x27, 0x94,
            0x97, 0x0d, 0x89, 0x81, 0xe6, 0x5d, 0x97, 0xb7,
            0x43, 0x4b, 0xa2, 0xca, 0x61, 0x71, 0x53, 0xee,
            0x55, 0xeb, 0x96, 0x50, 0xae, 0x41, 0x37, 0xc9,
            0x92, 0x5b, 0xb5, 0xf3, 0xb9, 0xac, 0x11, 0xa9,
            0xc8, 0xc1, 0x9e, 0xca, 0x8b, 0xd1, 0x11, 0x87,
            0x4f, 0x52, 0xff, 0xbd, 0x4a, 0x47, 0x9f, 0x14,
            0x64, 0x57, 0x45, 0xca, 0xd6, 0xf3, 0xcf, 0xf5,
            0x92, 0x01, 0xa0, 0x74, 0x1e, 0xc4, 0x56, 0xbb,
            0x78, 0x27, 0xb1, 0xb7, 0xcb, 0xec, 0x2c, 0xc5,
            0x67, 0x08, 0x10, 0xb8, 0xb1, 0x26, 0x3d, 0x92,
            // Public Exponent e (4 bytes: 65537 / 0x00010001)
            0x01, 0x00, 0x01, 0x00,
            // Message (13 bytes: "Test message.")
            'T', 'e', 's', 't', ' ', 'm', 'e', 's', 's', 'a', 'g', 'e', '.',
            // Padding (3 bytes 0x00 for 4-byte Ibex alignment)
            0x00, 0x00, 0x00,
            // Signature S (512 bytes)
            0xe6, 0x79, 0x15, 0x43, 0xfd, 0xc3, 0x4d, 0x4a,
            0x92, 0xee, 0x82, 0xdd, 0x2b, 0x98, 0x94, 0xee,
            0xe2, 0xf7, 0x05, 0xc0, 0x17, 0xb7, 0xe5, 0x85,
            0xf2, 0x9f, 0xc5, 0x60, 0xf2, 0xdf, 0x1d, 0x20,
            0xbe, 0x81, 0xf5, 0x96, 0xaa, 0xe3, 0x3f, 0x50,
            0x80, 0x81, 0x0f, 0xef, 0x2c, 0xf8, 0x7f, 0xb4,
            0xf8, 0x23, 0xa8, 0xc8, 0xa0, 0x8c, 0x73, 0x71,
            0x25, 0xcf, 0x3d, 0xb8, 0xc7, 0x90, 0xb9, 0x17,
            0xfa, 0xd7, 0xf1, 0xd9, 0x14, 0xba, 0xd3, 0x80,
            0x2f, 0x42, 0xff, 0x13, 0xde, 0x56, 0x6e, 0x9d,
            0xe0, 0x47, 0x2b, 0xb6, 0xbc, 0xb9, 0xf0, 0xa4,
            0x71, 0x9c, 0x0a, 0x94, 0x1c, 0x07, 0xb2, 0x69,
            0xdb, 0x4e, 0xe3, 0xdb, 0x32, 0xd9, 0x63, 0xfe,
            0x6f, 0xc1, 0xd9, 0xcc, 0x25, 0xed, 0xf4, 0x5e,
            0x46, 0x98, 0xc7, 0x1e, 0x58, 0x11, 0x21, 0x07,
            0x9d, 0x2c, 0xae, 0x8c, 0x5a, 0xef, 0xe2, 0x62,
            0xe0, 0xc4, 0x2c, 0x25, 0xda, 0xad, 0xba, 0xe8,
            0x33, 0x96, 0x42, 0xae, 0x43, 0x08, 0x9f, 0x42,
            0x00, 0x62, 0xdd, 0x40, 0xb0, 0x36, 0xc8, 0x04,
            0xdf, 0x9a, 0x40, 0x8c, 0xd1, 0xad, 0xb2, 0x73,
            0x74, 0x0a, 0xaa, 0x36, 0x9b, 0xef, 0xda, 0xfa,
            0x74, 0x1f, 0xee, 0xac, 0x0f, 0x18, 0x7b, 0x5b,
            0x40, 0x31, 0xad, 0x8f, 0xa2, 0x46, 0xc6, 0xce,
            0x5c, 0xdf, 0x8d, 0x40, 0x7f, 0xee, 0x38, 0x1d,
            0x59, 0xd4, 0x40, 0xf2, 0x5c, 0xc2, 0xdf, 0xfa,
            0xe4, 0x7e, 0x64, 0x97, 0xd5, 0x65, 0xd9, 0x42,
            0x16, 0xee, 0xf6, 0xdb, 0x35, 0xcf, 0x79, 0xc4,
            0xd3, 0x3c, 0xe3, 0x87, 0xce, 0xbf, 0x88, 0xac,
            0x6e, 0x52, 0x32, 0x6f, 0xe0, 0x1c, 0x80, 0xea,
            0x71, 0xee, 0xfe, 0x74, 0x64, 0xc4, 0xa6, 0x00,
            0xda, 0x7a, 0xb9, 0x8e, 0x2e, 0x3e, 0xb0, 0xb8,
            0x33, 0xd2, 0x43, 0x27, 0xca, 0x3b, 0x01, 0x4b,
            0x70, 0xa6, 0xe1, 0x9f, 0xc8, 0x87, 0xa9, 0x20,
            0xce, 0x1e, 0xe0, 0x0e, 0xcc, 0x17, 0xd6, 0xad,
            0xef, 0x54, 0xfa, 0xa3, 0x80, 0x7d, 0x09, 0x52,
            0xa2, 0x63, 0x95, 0x0a, 0x84, 0xfd, 0xdb, 0xb9,
            0xce, 0x35, 0x94, 0xf0, 0xe0, 0x3a, 0xeb, 0x98,
            0x20, 0xae, 0xbf, 0x51, 0x79, 0x4d, 0x8b, 0x6a,
            0xd8, 0xe7, 0x34, 0x47, 0x5c, 0x62, 0xc9, 0x0e,
            0xe2, 0x91, 0x64, 0x96, 0x9d, 0x5f, 0x3d, 0xb9,
            0x11, 0x98, 0xd3, 0x1e, 0xff, 0x1e, 0x7e, 0x81,
            0x8f, 0xa1, 0x9f, 0x50, 0xf9, 0xc2, 0x62, 0x76,
            0x86, 0x7f, 0xc8, 0x6b, 0x27, 0x00, 0x79, 0x75,
            0xad, 0xf1, 0x5a, 0xa7, 0x9e, 0x35, 0x7b, 0x3f,
            0x7a, 0x0f, 0x8b, 0x0e, 0x5d, 0xbe, 0x12, 0x28,
            0xbf, 0xb0, 0x22, 0xcf, 0xa1, 0xa9, 0xb8, 0xe8,
            0x0b, 0x27, 0xd1, 0xa4, 0x58, 0x2b, 0x0f, 0x99,
            0xfa, 0xd2, 0x04, 0xd6, 0xdd, 0x50, 0x01, 0x0c,
            0x4b, 0x3b, 0x57, 0x98, 0xfe, 0x11, 0xe9, 0x26,
            0x49, 0x6e, 0xc1, 0xc3, 0xb3, 0xd3, 0x32, 0x6e,
            0x31, 0x06, 0x19, 0x74, 0x6b, 0x40, 0x4c, 0x46,
            0x62, 0xce, 0x24, 0x81, 0xc5, 0x3e, 0x6c, 0x44,
            0x08, 0x2c, 0x5a, 0xde, 0x9b, 0x9f, 0xcf, 0xd0,
            0xca, 0x66, 0x5b, 0x1b, 0xfa, 0xe9, 0x59, 0x6e,
            0x4a, 0x72, 0x96, 0x9b, 0xe1, 0xee, 0xa5, 0x8c,
            0xa6, 0x1b, 0xa3, 0xe9, 0x85, 0x06, 0x82, 0xd7,
            0xf5, 0x7a, 0xf9, 0x77, 0x45, 0xb9, 0x0b, 0x3f,
            0x12, 0x5f, 0xe3, 0xba, 0xe8, 0x54, 0xcf, 0xd2,
            0x09, 0x89, 0xb5, 0xe0, 0x43, 0x99, 0xae, 0xa2,
            0x56, 0x34, 0xb0, 0x1e, 0x0b, 0xc4, 0xca, 0x5d,
            0xa0, 0x5f, 0xbf, 0x05, 0xc2, 0xd2, 0x45, 0xc7,
            0xfb, 0x04, 0x40, 0x62, 0x18, 0x19, 0x5c, 0x44,
            0x9d, 0x39, 0x53, 0x38, 0xe2, 0x2a, 0x8f, 0x73,
            0xa5, 0xa0, 0x1c, 0xd3, 0x53, 0x5e, 0xaf, 0x2d,
        },
    }
,
    .ecdsa_p256_sign = {
        .priv_key_len = 32,
        .ephemeral_len = 32,
        .msg_len = 32,
        .sig_len1 = 32,
        .sig_len2 = 32,
        .data = {
            // Private Key Scalar d (32 bytes)
            0x64, 0xb4, 0x72, 0xda, 0x6d, 0xa5, 0x54, 0xca,
            0xac, 0x3e, 0x4e, 0x0b, 0x13, 0xc8, 0x44, 0x5b,
            0x1a, 0x77, 0xf4, 0x59, 0xee, 0xa8, 0x4f, 0x1f,
            0x58, 0x8b, 0x5f, 0x71, 0x3d, 0x42, 0x9b, 0x51,
            // Ephemeral Secret Scalar k (32 bytes)
            0xde, 0x68, 0x2a, 0x64, 0x87, 0x07, 0x67, 0xb9,
            0x33, 0x5d, 0x4f, 0x82, 0x47, 0x62, 0x4a, 0x3b,
            0x7f, 0x3c, 0xe9, 0xf9, 0x45, 0xf2, 0x80, 0xa2,
            0x61, 0x6a, 0x90, 0x4b, 0xb1, 0xbb, 0xa1, 0x94,
            // Message Digest (32 bytes)
            0x44, 0xac, 0xf6, 0xb7, 0xe3, 0x6c, 0x13, 0x42,
            0xc2, 0xc5, 0x89, 0x72, 0x04, 0xfe, 0x09, 0x50,
            0x4e, 0x1e, 0x2e, 0xfb, 0x1a, 0x90, 0x03, 0x77,
            0xdb, 0xc4, 0xe7, 0xa6, 0xa1, 0x33, 0xec, 0x56,
            // Expected Signature (r || s, 64 bytes)
            0xac, 0xc2, 0xc8, 0x79, 0x6f, 0x5e, 0xbb, 0xca,
            0x7a, 0x5a, 0x55, 0x6a, 0x1f, 0x6b, 0xfd, 0x2a,
            0xed, 0x27, 0x95, 0x62, 0xd6, 0xe3, 0x43, 0x88,
            0x5b, 0x79, 0x14, 0xb5, 0x61, 0x80, 0xac, 0xf3,
            0x03, 0x89, 0x05, 0xcc, 0x2a, 0xda, 0xcd, 0x3c,
            0x5a, 0x17, 0x6f, 0xe9, 0x18, 0xb2, 0x97, 0xef,
            0x1c, 0x37, 0xf7, 0x2b, 0x26, 0x76, 0x6c, 0x78,
            0xb2, 0xa6, 0x05, 0xca, 0x19, 0x78, 0xf7, 0x8b,
        },
    }
,
    .ecdsa_p256_verify = {
        .pub_key_len1 = 32,
        .pub_key_len2 = 32,
        .msg_len = 32,
        .sig_len1 = 32,
        .sig_len2 = 32,
        .data = {
            // Public Key Coordinate Qx (32 bytes)
            0x83, 0xbf, 0x71, 0xc2, 0x46, 0xff, 0x59, 0x3c,
            0x2f, 0xb1, 0xbf, 0x4b, 0xe9, 0x5d, 0x56, 0xd3,
            0xcc, 0x8f, 0xdb, 0x48, 0xa2, 0xbf, 0x33, 0xf0,
            0xf4, 0xc7, 0x5f, 0x07, 0x1c, 0xe9, 0xcb, 0x1c,
            // Public Key Coordinate Qy (32 bytes)
            0xa9, 0x4c, 0x9a, 0xa8, 0x5c, 0xcd, 0x7c, 0xdc,
            0x78, 0x4e, 0x40, 0xb7, 0x93, 0xca, 0xb7, 0x6d,
            0xe0, 0x13, 0x61, 0x0e, 0x2c, 0xdb, 0x1f, 0x1a,
            0xa2, 0xf9, 0x11, 0x88, 0xc6, 0x14, 0x40, 0xce,
            // Message Digest (32 bytes)
            0x44, 0xac, 0xf6, 0xb7, 0xe3, 0x6c, 0x13, 0x42,
            0xc2, 0xc5, 0x89, 0x72, 0x04, 0xfe, 0x09, 0x50,
            0x4e, 0x1e, 0x2e, 0xfb, 0x1a, 0x90, 0x03, 0x77,
            0xdb, 0xc4, 0xe7, 0xa6, 0xa1, 0x33, 0xec, 0x56,
            // Signature (r || s, 64 bytes)
            0xac, 0xc2, 0xc8, 0x79, 0x6f, 0x5e, 0xbb, 0xca,
            0x7a, 0x5a, 0x55, 0x6a, 0x1f, 0x6b, 0xfd, 0x2a,
            0xed, 0x27, 0x95, 0x62, 0xd6, 0xe3, 0x43, 0x88,
            0x5b, 0x79, 0x14, 0xb5, 0x61, 0x80, 0xac, 0xf3,
            0x03, 0x89, 0x05, 0xcc, 0x2a, 0xda, 0xcd, 0x3c,
            0x5a, 0x17, 0x6f, 0xe9, 0x18, 0xb2, 0x97, 0xef,
            0x1c, 0x37, 0xf7, 0x2b, 0x26, 0x76, 0x6c, 0x78,
            0xb2, 0xa6, 0x05, 0xca, 0x19, 0x78, 0xf7, 0x8b,
        },
    }
,
    .ecdsa_p384_sign = {
        .priv_key_len = 48,
        .ephemeral_len = 48,
        .msg_len = 48,
        .sig_len1 = 48,
        .sig_len2 = 48,
        .data = {
            // Private Key Scalar d (48 bytes)
            0x6b, 0x9e, 0x7f, 0x6d, 0x47, 0x87, 0xc9, 0x83,
            0x77, 0x5a, 0x85, 0x9b, 0xd9, 0xf0, 0x52, 0x4b,
            0x18, 0x30, 0x26, 0x16, 0x58, 0xf0, 0x89, 0x2a,
            0xc4, 0x6c, 0x67, 0x74, 0x72, 0x20, 0xf7, 0x84,
            0x2c, 0x83, 0xe0, 0x61, 0x96, 0x56, 0xa6, 0x11,
            0xc3, 0x92, 0x45, 0xa3, 0x74, 0xbc, 0x02, 0xc6,
            // Ephemeral Secret Scalar k (48 bytes)
            0x43, 0x24, 0xa3, 0xf3, 0x24, 0x7e, 0x87, 0x04,
            0xa8, 0xd4, 0xea, 0x36, 0x3d, 0xcd, 0x0f, 0xb3,
            0xcc, 0x57, 0xc7, 0x6c, 0xaf, 0xe7, 0xd1, 0x0d,
            0x8c, 0x79, 0x9b, 0x29, 0xb5, 0x96, 0x24, 0x93,
            0xc0, 0xcd, 0x97, 0x86, 0xd8, 0xd0, 0x27, 0x78,
            0x0b, 0x3d, 0x68, 0xc4, 0x25, 0x5c, 0x0b, 0xc1,
            // Message Digest (48 bytes)
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0xbb, 0xbd, 0x0a, 0x5f, 0x64, 0x5d, 0x3f, 0xda,
            0x10, 0xe2, 0x88, 0xd1, 0x72, 0xb2, 0x99, 0x45,
            0x5f, 0x9d, 0xff, 0x00, 0xe0, 0xfb, 0xc2, 0x83,
            0x3e, 0x18, 0xcd, 0x01, 0x7d, 0x7f, 0x3e, 0xd1,
            // Expected Signature: R || S (96 bytes)
            // R (48 bytes)
            0x78, 0xe8, 0x40, 0xd4, 0x46, 0x79, 0x26, 0xc3,
            0x2e, 0xaa, 0x88, 0x17, 0x85, 0x61, 0x8c, 0x97,
            0x59, 0x03, 0xab, 0xa0, 0x1d, 0x55, 0x54, 0x90,
            0x60, 0xad, 0xc2, 0xeb, 0xd7, 0x7e, 0x47, 0x48,
            0x59, 0x78, 0x02, 0xcd, 0x38, 0x3f, 0x48, 0xd4,
            0x86, 0x32, 0xf5, 0xda, 0x0c, 0xb0, 0x1d, 0xb1,
            // S (48 bytes)
            0xf2, 0xcb, 0xf8, 0x7d, 0x02, 0xac, 0x48, 0x10,
            0x67, 0x87, 0x78, 0x4b, 0xe7, 0x27, 0x8b, 0xc9,
            0xd7, 0x12, 0x65, 0x07, 0x5a, 0x06, 0xf5, 0x2f,
            0x76, 0x3a, 0x68, 0x9c, 0x31, 0xe3, 0xb6, 0xe2,
            0xe8, 0x73, 0xe9, 0xfe, 0xa8, 0x12, 0x81, 0xe6,
            0x4c, 0x60, 0xb0, 0xc5, 0x73, 0x78, 0x00, 0x16,
        },
    }
,
    .ecdsa_p384_verify = {
        .pub_key_len1 = 48,
        .pub_key_len2 = 48,
        .msg_len = 48,
        .sig_len1 = 48,
        .sig_len2 = 48,
        .data = {
            // Public Key Coordinate Qx (48 bytes)
            0x75, 0xbc, 0x65, 0x07, 0x4c, 0x67, 0x88, 0xab,
            0xbf, 0x82, 0xc2, 0xb9, 0x4c, 0x27, 0x09, 0xe9,
            0x39, 0x04, 0x0b, 0xbb, 0x86, 0x7f, 0x04, 0xb7,
            0xf6, 0x9f, 0xd4, 0x97, 0x1c, 0x04, 0x45, 0xd1,
            0x6d, 0xe9, 0xd3, 0x53, 0x94, 0x6e, 0x82, 0x59,
            0xd0, 0x7c, 0xf0, 0x21, 0x3b, 0x19, 0x00, 0x04,
            // Public Key Coordinate Qy (48 bytes)
            0x47, 0xa1, 0x82, 0x6b, 0x92, 0x4a, 0x23, 0x2f,
            0x8e, 0xc9, 0x5e, 0x0c, 0x5b, 0x42, 0x9a, 0xec,
            0x42, 0x8f, 0xdf, 0x1a, 0xd1, 0x5d, 0xba, 0x9e,
            0xe9, 0x95, 0xcf, 0x2d, 0xf6, 0x6a, 0xb7, 0x69,
            0x7f, 0x6d, 0xc7, 0x75, 0xae, 0xc5, 0xd2, 0x68,
            0x04, 0xc7, 0xcb, 0x2a, 0xc5, 0x89, 0x0d, 0xf7,
            // Message Digest (48 bytes)
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0xbb, 0xbd, 0x0a, 0x5f, 0x64, 0x5d, 0x3f, 0xda,
            0x10, 0xe2, 0x88, 0xd1, 0x72, 0xb2, 0x99, 0x45,
            0x5f, 0x9d, 0xff, 0x00, 0xe0, 0xfb, 0xc2, 0x83,
            0x3e, 0x18, 0xcd, 0x01, 0x7d, 0x7f, 0x3e, 0xd1,
            // Signature: R || S (96 bytes)
            // R (48 bytes)
            0x78, 0xe8, 0x40, 0xd4, 0x46, 0x79, 0x26, 0xc3,
            0x2e, 0xaa, 0x88, 0x17, 0x85, 0x61, 0x8c, 0x97,
            0x59, 0x03, 0xab, 0xa0, 0x1d, 0x55, 0x54, 0x90,
            0x60, 0xad, 0xc2, 0xeb, 0xd7, 0x7e, 0x47, 0x48,
            0x59, 0x78, 0x02, 0xcd, 0x38, 0x3f, 0x48, 0xd4,
            0x86, 0x32, 0xf5, 0xda, 0x0c, 0xb0, 0x1d, 0xb1,
            // S (48 bytes)
            0xf2, 0xcb, 0xf8, 0x7d, 0x02, 0xac, 0x48, 0x10,
            0x67, 0x87, 0x78, 0x4b, 0xe7, 0x27, 0x8b, 0xc9,
            0xd7, 0x12, 0x65, 0x07, 0x5a, 0x06, 0xf5, 0x2f,
            0x76, 0x3a, 0x68, 0x9c, 0x31, 0xe3, 0xb6, 0xe2,
            0xe8, 0x73, 0xe9, 0xfe, 0xa8, 0x12, 0x81, 0xe6,
            0x4c, 0x60, 0xb0, 0xc5, 0x73, 0x78, 0x00, 0x16,
        },
    }
,
    .ed25519_sign = {
        .priv_key_len = 32,
        .ephemeral_len = 0,
        .msg_len = 1,
        .sig_len1 = 32,
        .sig_len2 = 32,
        .data = {
            // Private Key Seed (32 bytes)
            0x4c, 0xcd, 0x08, 0x9b, 0x28, 0xff, 0x96, 0xda,
            0x9d, 0xb6, 0xc3, 0x46, 0xec, 0x11, 0x4e, 0x0f,
            0x5b, 0x8a, 0x31, 0x9f, 0x35, 0xab, 0xa6, 0x24,
            0xda, 0x8c, 0xf6, 0xed, 0x4f, 0xb8, 0xa6, 0xfb,
            // Message (1 byte: 0x72)
            0x72,
            // Padding (3 bytes 0x00 for 4-byte Ibex alignment)
            0x00, 0x00, 0x00,
            // Expected Signature R || S (64 bytes)
            // R (32 bytes)
            0xda, 0x69, 0xdb, 0xeb, 0x23, 0x22, 0x76, 0xb3,
            0x8f, 0x3f, 0x50, 0x16, 0x54, 0x7b, 0xb2, 0xa2,
            0x40, 0x25, 0x64, 0x5f, 0x0b, 0x82, 0x0e, 0x72,
            0xb8, 0xca, 0xd4, 0xf0, 0xa9, 0x09, 0xa0, 0x92,
            // S (32 bytes)
            0x08, 0x5a, 0xc1, 0xe4, 0x3e, 0x15, 0x99, 0x6e,
            0x45, 0x8f, 0x36, 0x13, 0xd0, 0xf1, 0x1d, 0x8c,
            0x38, 0x7b, 0x2e, 0xae, 0xb4, 0x30, 0x2a, 0xee,
            0xb0, 0x0d, 0x29, 0x16, 0x12, 0xbb, 0x0c, 0x00,
        },
    }
,
    .ed25519_verify = {
        .pub_key_len1 = 32,
        .pub_key_len2 = 0,
        .msg_len = 1,
        .sig_len1 = 32,
        .sig_len2 = 32,
        .data = {
            // Public Key (32 bytes)
            0x3d, 0x40, 0x17, 0xc3, 0xe8, 0x43, 0x89, 0x5a,
            0x92, 0xb7, 0x0a, 0xa7, 0x4d, 0x1b, 0x7e, 0xbc,
            0x9c, 0x98, 0x2c, 0xcf, 0x2e, 0xc4, 0x96, 0x8c,
            0xc0, 0xcd, 0x55, 0xf1, 0x2a, 0xf4, 0x66, 0x0c,
            // Message (1 byte: 0x72)
            0x72,
            // Padding (3 bytes 0x00 for 4-byte Ibex alignment)
            0x00, 0x00, 0x00,
            // Signature R || S (64 bytes)
            // R (32 bytes)
            0xda, 0x69, 0xdb, 0xeb, 0x23, 0x22, 0x76, 0xb3,
            0x8f, 0x3f, 0x50, 0x16, 0x54, 0x7b, 0xb2, 0xa2,
            0x40, 0x25, 0x64, 0x5f, 0x0b, 0x82, 0x0e, 0x72,
            0xb8, 0xca, 0xd4, 0xf0, 0xa9, 0x09, 0xa0, 0x92,
            // S (32 bytes)
            0x08, 0x5a, 0xc1, 0xe4, 0x3e, 0x15, 0x99, 0x6e,
            0x45, 0x8f, 0x36, 0x13, 0xd0, 0xf1, 0x1d, 0x8c,
            0x38, 0x7b, 0x2e, 0xae, 0xb4, 0x30, 0x2a, 0xee,
            0xb0, 0x0d, 0x29, 0x16, 0x12, 0xbb, 0x0c, 0x00,
        },
    }
,
};

/**
 * Macro computing exact byte offset of a vector payload from
 * the start of `kFipsKatDescriptorTable`.
 */
#define FIPS_KAT_OFFSET(field) \
  (sizeof(fips_kat_rom_table_t) + offsetof(fips_kat_data_store_t, field))

/**
 * Concrete descriptor table in ROM holding 19 entries.
 */
#define FIPS_KAT_NUM_ENTRIES 19

/**
 * Concrete descriptor table in ROM holding 19 entries.
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
            {
                .algorithm_id = (uint32_t)kFipsKatAlgShake256,
                .offset = FIPS_KAT_OFFSET(shake256),
                .size = sizeof(fips_kat_shake256_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgKmac256,
                .offset = FIPS_KAT_OFFSET(kmac256),
                .size = sizeof(fips_kat_kmac256_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgAesEcb256Decrypt,
                .offset = FIPS_KAT_OFFSET(aes_ecb256),
                .size = sizeof(fips_kat_aes_ecb256_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgAesCbc256Decrypt,
                .offset = FIPS_KAT_OFFSET(aes_cbc256),
                .size = sizeof(fips_kat_aes_cbc256_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgAesKwp256Wrap,
                .offset = FIPS_KAT_OFFSET(aes_kwp256),
                .size = sizeof(fips_kat_aes_kwp256_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgKdfHmacSha2_256,
                .offset = FIPS_KAT_OFFSET(kdf_hmac_sha256),
                .size = sizeof(fips_kat_kdf_hmac_sha256_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgKdfKmac256,
                .offset = FIPS_KAT_OFFSET(kdf_kmac256),
                .size = sizeof(fips_kat_kdf_kmac256_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgRsa4096Sign,
                .offset = FIPS_KAT_OFFSET(rsa_4096_sign),
                .size = sizeof(fips_kat_rsa_4096_sign_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgRsa4096Verify,
                .offset = FIPS_KAT_OFFSET(rsa_4096_verify),
                .size = sizeof(fips_kat_rsa_4096_verify_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgEcdsaP256Sign,
                .offset = FIPS_KAT_OFFSET(ecdsa_p256_sign),
                .size = sizeof(fips_kat_ecdsa_p256_sign_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgEcdsaP256Verify,
                .offset = FIPS_KAT_OFFSET(ecdsa_p256_verify),
                .size = sizeof(fips_kat_ecdsa_p256_verify_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgEcdsaP384Sign,
                .offset = FIPS_KAT_OFFSET(ecdsa_p384_sign),
                .size = sizeof(fips_kat_ecdsa_p384_sign_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgEcdsaP384Verify,
                .offset = FIPS_KAT_OFFSET(ecdsa_p384_verify),
                .size = sizeof(fips_kat_ecdsa_p384_verify_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgEd25519Sign,
                .offset = FIPS_KAT_OFFSET(ed25519_sign),
                .size = sizeof(fips_kat_ed25519_sign_t),
            },
            {
                .algorithm_id = (uint32_t)kFipsKatAlgEd25519Verify,
                .offset = FIPS_KAT_OFFSET(ed25519_verify),
                .size = sizeof(fips_kat_ed25519_verify_t),
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
