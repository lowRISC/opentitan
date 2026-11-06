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
 * Concrete descriptor table in ROM holding 11 entries.
 */
#define FIPS_KAT_NUM_ENTRIES 11

/**
 * Concrete descriptor table in ROM holding 11 entries.
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
