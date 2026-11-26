// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_FIPS_KAT_TABLE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_FIPS_KAT_TABLE_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"

#ifdef __cplusplus
extern "C" {
#endif

enum {
  /**
   * Magic number identifying the FIPS KAT descriptor table ("FKAT" in ASCII).
   */
  kFipsKatDescriptorMagic = 0x464B4154,
  /**
   * Supported version for the FIPS KAT descriptor table structure.
   */
  kFipsKatDescriptorVersion1 = 1,
  /**
   * Fixed offset from the top of ROM to the start of the 8 KiB NAPOT-aligned
   * FIPS KAT region: `[rom_end - kFipsKatRomEndOffset, rom_end)`.
   *
   * On Earl Grey Gen2 (192 KiB ROM at `[0x40000, 0x70000)`), this places the
   * descriptor table directly at `0x6E000` within the 8 KiB NAPOT window
   * `[0x6E000, 0x70000)`, leaving 184 KiB below for Mask ROM code and
   * read-only data with zero dead gap.
   *
   * Transient BL0 ePMP maps `kFipsKatRegionSize` (8 KiB NAPOT) read-only,
   * while descriptor/data helpers take `kFipsKatMaxTableSize` (`0x1F80`) so
   * valid offsets never enter `.chip_info` (`[0x6FF80, 0x6FFE0)`) or the
   * ECC-poisoned `rom_ctrl` digest words (`[0x6FFE0, 0x70000)`).
   */
  kFipsKatRomEndOffset = 0x2000,
  /**
   * Fixed size of the NAPOT-aligned FIPS KAT ROM ePMP window (8 KiB).
   */
  kFipsKatRegionSize = 0x2000,
  /**
   * Reserved bytes at the top of ROM for `.chip_info` (`[0x6FF80, 0x6FFE0)`)
   * and the ECC-poisoned `rom_ctrl` digest words (`[0x6FFE0, 0x70000)`).
   */
  kFipsKatChipInfoReservedBytes = 128,
  /**
   * Maximum usable size of the FIPS KAT descriptor table and payloads within
   * the 8 KiB NAPOT window (`0x1F80` = 8,064 bytes). Pass this bound (not
   * `kFipsKatRegionSize`) to descriptor/data helpers so valid offsets never
   * enter `.chip_info` or `[0x6FFE0, 0x70000)`.
   */
  kFipsKatMaxTableSize = kFipsKatRegionSize - kFipsKatChipInfoReservedBytes,
  /**
   * Fixed payload size (in bytes) of each sparse signature chunk in
   * `fips_kat_sparse_chunk_t` (matches SLH-DSA-SHA2-128s hash size `n = 16`).
   */
  kFipsKatSparseChunkBytes = 16,
};

/**
 * Rounds a byte length up to the next 4-byte boundary.
 *
 * Uniform Binary Payload ABI Rule:
 * Every variable-length sub-field inside payload `data[]` arrays is padded
 * with trailing `0x00` bytes to a 4-byte boundary (`FIPS_KAT_ALIGN4(len)`).
 * Every sub-field therefore begins at a 4-byte aligned offset relative to the
 * start of its payload struct, ensuring trap-free single-word loads on RISC-V
 * Ibex and UBSan-clean word accesses.
 */
#define FIPS_KAT_ALIGN4(len) (((size_t)(len) + 3u) & ~(size_t)3u)

/**
 * Unique identifiers for cryptographic algorithms with KAT vectors.
 *
 * NOTE: Values are permanent tokens on taped-out silicon. Never renumber or
 * reuse existing values.
 */
typedef enum fips_kat_alg_id {
  kFipsKatAlgNone = 0,

  // SHA-2 & HMAC (256 & 512)
  kFipsKatAlgSha2_256 = 1,
  kFipsKatAlgSha2_512 = 2,
  kFipsKatAlgHmacSha2_256 = 3,
  kFipsKatAlgHmacSha2_512 = 4,

  // SHA-3 / Keccak
  kFipsKatAlgShake256 = 5,
  kFipsKatAlgKmac256 = 6,

  // AES Block Cipher & Key Wrap (256-bit)
  kFipsKatAlgAesEcb256Decrypt = 7,
  kFipsKatAlgAesCbc256Decrypt = 8,
  kFipsKatAlgAesKwp256Wrap = 9,

  // Key Derivation (SP 800-108r1 KDF)
  kFipsKatAlgKdfHmacSha2_256 = 10,
  kFipsKatAlgKdfKmac256 = 11,

  // RSA Asymmetric (2048 & 4096, PKCS#1 v1.5)
  kFipsKatAlgRsa2048Verify = 12,
  kFipsKatAlgRsa4096 = 13,  // Shared RSA-4096 Sign & Verify
  // ID 14 reserved (merged into kFipsKatAlgRsa4096).

  // Elliptic Curve Signatures (ECDSA & Ed25519)
  kFipsKatAlgEcdsaP256Sign = 15,
  kFipsKatAlgEcdsaP256Verify = 16,
  kFipsKatAlgEcdsaP384Sign = 17,
  kFipsKatAlgEcdsaP384Verify = 18,
  kFipsKatAlgEd25519Sign = 19,
  kFipsKatAlgEd25519Verify = 20,

  // Key Agreement / ECDH (P-256, P-384, X25519)
  kFipsKatAlgEcdhP256 = 21,
  kFipsKatAlgEcdhP384 = 22,
  kFipsKatAlgX25519 = 23,

  // Post-Quantum Cryptography (FIPS 204 ML-DSA & FIPS 203 ML-KEM)
  kFipsKatAlgMldsa87 = 24,
  kFipsKatAlgMlkem1024 = 25,

  // DRBG & Entropy Source Conditioning (SP 800-90A & SP 800-90B)
  kFipsKatAlgDrbgAes256 = 26,
  kFipsKatAlgEntropySrcSha3Conditioning = 27,

  // Authenticated Encryption (AES-256-GCM)
  kFipsKatAlgAesGcm256Encrypt = 28,

  // FIPS 205 SLH-DSA-SHA2-128s / SPHINCS+-SHA2-128s-simple Verification
  // (compact sparse-signature format via `sparse_verify_kat_data_t`; FIPS 205
  // pure-mode `ctx = ""`, compatible with OpenTitan `sigverify/sphincsplus`
  // using `msg_prefix_1 = {0x00, 0x00}`).
  kFipsKatAlgSphincsPlusSha2_128sVerify = 29,

  // Key Derivation (HKDF-SHA2-384 - RFC 5869 / SP 800-56Cr2)
  kFipsKatAlgHkdfSha2_384 = 30,

  // SHA-2 (384-bit for CNSA 2.0)
  kFipsKatAlgSha2_384 = 31,
} fips_kat_alg_id_t;

/**
 * Entry describing the location of a single algorithm test vector payload.
 */
typedef struct fips_kat_entry {
  uint16_t algorithm_id;  // fips_kat_alg_id_t
  uint16_t reserved;      // Must be 0
  uint16_t offset;  // Byte offset from start of descriptor table (4B-aligned)
  uint16_t size;    // Byte size of serialized payload block (4B-aligned)
} fips_kat_entry_t;

OT_ASSERT_SIZE(fips_kat_entry_t, 8);
OT_ASSERT_MEMBER_OFFSET(fips_kat_entry_t, algorithm_id, 0);
OT_ASSERT_MEMBER_OFFSET(fips_kat_entry_t, reserved, 2);
OT_ASSERT_MEMBER_OFFSET(fips_kat_entry_t, offset, 4);
OT_ASSERT_MEMBER_OFFSET(fips_kat_entry_t, size, 6);

/**
 * Root table pinned at the start of the `.fips_kat` ROM region describing all
 * embedded KAT vectors.
 */
typedef struct fips_kat_descriptor_table {
  uint32_t magic;        // Must be kFipsKatDescriptorMagic (0x464B4154)
  uint32_t version;      // Must be kFipsKatDescriptorVersion1 (1)
  uint32_t entry_count;  // Number of entries in entries[]
  uint32_t total_size;   // Total size of descriptor table + payloads in bytes
  fips_kat_entry_t entries[];
} fips_kat_descriptor_table_t;

OT_ASSERT_SIZE(fips_kat_descriptor_table_t, 16);
OT_ASSERT_MEMBER_OFFSET(fips_kat_descriptor_table_t, magic, 0);
OT_ASSERT_MEMBER_OFFSET(fips_kat_descriptor_table_t, version, 4);
OT_ASSERT_MEMBER_OFFSET(fips_kat_descriptor_table_t, entry_count, 8);
OT_ASSERT_MEMBER_OFFSET(fips_kat_descriptor_table_t, total_size, 12);
OT_ASSERT_MEMBER_OFFSET(fips_kat_descriptor_table_t, entries, 16);

/**
 * ============================================================================
 * Vector Payload Schemas (Uniform 4-byte Sub-Field Alignment)
 * ============================================================================
 * All payload schema length fields are uniformly `uint16_t` with explicit
 * `uint16_t reserved` (= 0) padding on odd-field schemas so every `data[]`
 * array begins strictly at `0 mod 4`.
 *
 * All variable-length byte slices inside `data[]` are individually padded to
 * `FIPS_KAT_ALIGN4(len)`. Use the inline accessors below to resolve sub-fields
 * and verify `entry->size`.
 */

// 1. Hash / HMAC / SHAKE / Entropy Conditioning
typedef struct hmac_kat_data {
  uint16_t key_len;
  uint16_t msg_len;
  uint16_t digest_len;
  uint16_t reserved;  // Must be 0
  uint8_t data[];     // pad4(key) || pad4(msg) || pad4(expected_digest)
} hmac_kat_data_t;

OT_ASSERT_SIZE(hmac_kat_data_t, 8);
OT_ASSERT_MEMBER_OFFSET(hmac_kat_data_t, data, 8);

// 2. KMAC / SP 800-108r1 KDF (KMAC-256, KDF-CTR-HMAC-SHA256, KDF-KMAC-256)
typedef struct kdf_kat_data {
  uint16_t key_len;
  uint16_t label_len;    // KMAC customization string S or SP 800-108r1 Label
  uint16_t context_len;  // KMAC input message or SP 800-108r1 Context
  uint16_t out_len;      // Expected MAC tag or derived keying material
  uint8_t data[];  // pad4(key) || pad4(label) || pad4(context) || pad4(out)
} kdf_kat_data_t;

OT_ASSERT_SIZE(kdf_kat_data_t, 8);
OT_ASSERT_MEMBER_OFFSET(kdf_kat_data_t, data, 8);

// 3. Symmetric Block Cipher / AEAD / Key Wrap (AES-256 ECB, CBC, KWP, GCM)
typedef struct aes_kat_data {
  uint16_t key_len;
  uint16_t iv_len;
  uint16_t aad_len;
  uint16_t pt_len;
  uint16_t ct_len;
  uint16_t tag_len;
  uint8_t
      data[];  // pad4(key)||pad4(iv)||pad4(aad)||pad4(pt)||pad4(ct)||pad4(tag)
} aes_kat_data_t;

OT_ASSERT_SIZE(aes_kat_data_t, 12);
OT_ASSERT_MEMBER_OFFSET(aes_kat_data_t, data, 12);

// 4. Asymmetric Verification (RSA-2048, ECDSA, Ed25519)
// Endianness conventions (matching OpenTitan cryptolib / OTBN):
// - RSA-2048: pub_key1 = N (LE words), pub_key2 = e (LE u32), msg = raw,
//   sig1 = S (LE words), sig2 = empty.
// - ECDSA P-256/P-384: pub_key1 = Qx (LE), pub_key2 = Qy (LE), msg = raw CAVP
//   message (hashed with SHA-256 for P-256, SHA-384 for P-384),
//   sig1 = R (LE), sig2 = S (LE).
// - Ed25519: pub_key1 = pk (RFC 8032), pub_key2 = empty, msg = raw,
//   sig1 = R (RFC 8032), sig2 = S (RFC 8032).
// (RSA-4096 Sign & Verify shares Schema 5; SLH-DSA / SPHINCS+ uses Schema 11
// `sparse_verify_kat_data_t`.)
typedef struct asymmetric_verify_kat_data {
  uint16_t pub_key_len1;
  uint16_t pub_key_len2;
  uint16_t msg_len;
  uint16_t sig_len1;
  uint16_t sig_len2;
  uint16_t reserved;  // Must be 0
  uint8_t data[];     // pad4(pk1)||pad4(pk2)||pad4(msg)||pad4(sig1)||pad4(sig2)
} asymmetric_verify_kat_data_t;

OT_ASSERT_SIZE(asymmetric_verify_kat_data_t, 12);
OT_ASSERT_MEMBER_OFFSET(asymmetric_verify_kat_data_t, data, 12);

// 5. Asymmetric Signing & Combined Keypair (RSA-4096, ECDSA P-256/P-384,
// Ed25519)
// Endianness conventions:
// - RSA-4096 (Sign & Verify): priv_key = N (512 B) || D (512 B) in LE words,
//   ephemeral = e (4 B LE u32, 65537), msg = raw, sig1 = S (512 B LE words),
//   sig2 = empty.
// - ECDSA P-256/P-384: priv_key = d (LE), ephemeral = k (LE), msg = raw CAVP
//   message (hashed with SHA-256 / SHA-384), sig1 = R (LE), sig2 = S (LE).
// - Ed25519: priv_key = seed (RFC 8032), ephemeral = empty, msg = raw,
//   sig1 = R (RFC 8032), sig2 = S (RFC 8032).
typedef struct asymmetric_sign_kat_data {
  uint16_t priv_key_len;
  uint16_t ephemeral_len;
  uint16_t msg_len;
  uint16_t sig_len1;
  uint16_t sig_len2;
  uint16_t reserved;  // Must be 0
  uint8_t data[];  // pad4(priv)||pad4(eph)||pad4(msg)||pad4(sig1)||pad4(sig2)
} asymmetric_sign_kat_data_t;

OT_ASSERT_SIZE(asymmetric_sign_kat_data_t, 12);
OT_ASSERT_MEMBER_OFFSET(asymmetric_sign_kat_data_t, data, 12);

// 6. Key Agreement (ECDH P-256/P-384, X25519)
// Endianness conventions:
// - ECDH P-256/P-384: priv_key = d (LE), pub_key1 = Qx (LE), pub_key2 = Qy
//   (LE), shared_secret = Zx (LE).
// - X25519: priv_key = sk (RFC 7748), pub_key1 = peer_pk, pub_key2 = empty,
//   shared_secret = ss (RFC 7748).
typedef struct ecdh_kat_data {
  uint16_t priv_key_len;
  uint16_t pub_key_len1;
  uint16_t pub_key_len2;
  uint16_t shared_secret_len;
  uint8_t data[];  // pad4(priv)||pad4(pk1)||pad4(pk2)||pad4(shared_secret)
} ecdh_kat_data_t;

OT_ASSERT_SIZE(ecdh_kat_data_t, 8);
OT_ASSERT_MEMBER_OFFSET(ecdh_kat_data_t, data, 8);

// 7. Post-Quantum Signatures (ML-DSA-87 ACVP Dynamic Rejection Cases)
typedef struct fips_kat_mldsa87_case {
  uint8_t seed[32];   /**< 32-byte seed xi for deterministic keygen */
  uint8_t mprime[32]; /**< 32-byte M' message */
  uint8_t expected_sig_hash[32]; /**< SHA2-256(sig[0..4627]) */
} fips_kat_mldsa87_case_t;

OT_ASSERT_SIZE(fips_kat_mldsa87_case_t, 96);

typedef struct mldsa_kat_data {
  uint16_t num_cases; /**< Number of test cases in `cases[]` */
  uint16_t reserved;  /**< Must be 0 */
  fips_kat_mldsa87_case_t cases[];
} mldsa_kat_data_t;

OT_ASSERT_SIZE(mldsa_kat_data_t, 4);
OT_ASSERT_MEMBER_OFFSET(mldsa_kat_data_t, cases, 4);

// 8. CTR_DRBG AES-256 (NIST SP 800-90A Section 11.3, no df, PR=True)
// Matches `sw/device/lib/crypto/drivers/entropy_kat.c`:
// - Seeds and internal-state `(reseed_counter, V, Key)` 32-bit words are in
//   CSRNG reversed word order relative to NIST CAVP hex strings.
// - `expected_output` is in forward word order matching
//   `entropy_csrng_generate_data_get()`.
typedef struct drbg_kat_state {
  uint32_t reseed_counter;
  uint32_t v[4];
  uint32_t key[8];
} drbg_kat_state_t;

OT_ASSERT_SIZE(drbg_kat_state_t, 52);

typedef struct drbg_kat_data {
  uint16_t seed_len;             // 48 bytes (12 words) per seed
  uint16_t expected_output_len;  // 64 bytes (16 words)
  uint32_t seed_instantiate[12];
  uint32_t seed_reseed1[12];
  uint32_t seed_reseed2[12];
  drbg_kat_state_t state_instantiate;
  drbg_kat_state_t state_reseed1;
  drbg_kat_state_t state_generate1;
  drbg_kat_state_t state_reseed2;
  drbg_kat_state_t state_generate2;
  uint32_t expected_output[16];
} drbg_kat_data_t;

OT_ASSERT_SIZE(drbg_kat_data_t, 472);
OT_ASSERT_MEMBER_OFFSET(drbg_kat_data_t, seed_instantiate, 4);

// 9. Key Encapsulation (FIPS 203 ML-KEM-1024 DKG + DED + OH)
typedef struct kem_kat_data {
  uint16_t seed_d_len;
  uint16_t seed_z_len;
  uint16_t seed_m_len;
  uint16_t exp_pk_hash_len;
  uint16_t exp_ct_hash_len;
  uint16_t exp_ss_len;
  uint8_t
      data[];  // pad4(d)||pad4(z)||pad4(m)||pad4(pk_h)||pad4(ct_h)||pad4(ss)
} kem_kat_data_t;

OT_ASSERT_SIZE(kem_kat_data_t, 12);
OT_ASSERT_MEMBER_OFFSET(kem_kat_data_t, data, 12);

// 10. Key Derivation (HKDF - RFC 5869 / SP 800-56Cr2)
typedef struct hkdf_kat_data {
  uint16_t ikm_len;
  uint16_t salt_len;
  uint16_t info_len;
  uint16_t prk_len;
  uint16_t okm_len;
  uint16_t reserved;  // Must be 0
  uint8_t data[];     // pad4(ikm)||pad4(salt)||pad4(info)||pad4(prk)||pad4(okm)
} hkdf_kat_data_t;

OT_ASSERT_SIZE(hkdf_kat_data_t, 12);
OT_ASSERT_MEMBER_OFFSET(hkdf_kat_data_t, data, 12);

// 11. Sparse-Signature Asymmetric Verification
// (FIPS 205 SLH-DSA-SHA2-128s / SPHINCS+-SHA2-128s-simple)
//
// Encodes a large predominantly-zero signature as a sequence of strictly
// ascending, non-overlapping fixed 16-byte chunks placed at 16-byte-aligned
// offsets over a zero-initialized output buffer. Every chunk struct is 20 B
// (4-byte aligned).
typedef struct fips_kat_sparse_chunk {
  uint16_t offset;    // 16-byte-aligned byte offset into output signature
  uint16_t reserved;  // Must be 0
  uint8_t data[kFipsKatSparseChunkBytes];
} fips_kat_sparse_chunk_t;

OT_ASSERT_SIZE(fips_kat_sparse_chunk_t, 20);
OT_ASSERT_MEMBER_OFFSET(fips_kat_sparse_chunk_t, offset, 0);
OT_ASSERT_MEMBER_OFFSET(fips_kat_sparse_chunk_t, reserved, 2);
OT_ASSERT_MEMBER_OFFSET(fips_kat_sparse_chunk_t, data, 4);

typedef struct sparse_verify_kat_data {
  uint16_t pub_key_len;
  uint16_t msg_len;
  uint16_t sig_len;     // Expanded signature length in bytes (e.g. 7856)
  uint16_t num_chunks;  // Number of fixed 16-byte sparse signature chunks
  uint8_t data[];       // pad4(pk) || pad4(msg) || sparse_chunks[num_chunks]
} sparse_verify_kat_data_t;

OT_ASSERT_SIZE(sparse_verify_kat_data_t, 8);
OT_ASSERT_MEMBER_OFFSET(sparse_verify_kat_data_t, data, 8);

/**
 * ============================================================================
 * Descriptor Table Validation & Lookup Helpers (Top-Agnostic)
 * ============================================================================
 */

/**
 * Validates a FIPS KAT descriptor table bounded by `region_size`.
 *
 * @param table Pointer to descriptor table.
 * @param region_size Maximum valid byte size of the table + payloads region
 *                    (e.g., `kFipsKatMaxTableSize`, excluding `.chip_info` and
 *                    `rom_ctrl` digest words).
 * @return True if table passes alignment, magic, version, size, and entry
 *         count checks.
 */
OT_WARN_UNUSED_RESULT
static inline bool validate_fips_descriptor_table(
    const fips_kat_descriptor_table_t *table, size_t region_size) {
  if (table == NULL || ((uintptr_t)table & 0x3u) != 0 ||
      region_size < sizeof(fips_kat_descriptor_table_t)) {
    return false;
  }
  const uint32_t magic = table->magic;
  const uint32_t version = table->version;
  const uint32_t entry_count = table->entry_count;
  const uint32_t total_size = table->total_size;
  if (magic != kFipsKatDescriptorMagic ||
      version != kFipsKatDescriptorVersion1 ||
      total_size < sizeof(fips_kat_descriptor_table_t) ||
      (total_size & 0x3u) != 0 || (size_t)total_size > region_size) {
    return false;
  }
  const uint32_t max_entries =
      (total_size - (uint32_t)sizeof(fips_kat_descriptor_table_t)) /
      (uint32_t)sizeof(fips_kat_entry_t);
  return entry_count <= max_entries;
}

/**
 * Returns a validated pointer to the FIPS KAT descriptor table anchored at
 * `region_base` within a window of `region_size` bytes.
 *
 * @param region_base Base address of the mapped FIPS KAT region (e.g.,
 *                    `rom_base + rom_size - kFipsKatRomEndOffset`).
 * @param region_size Usable table bound in bytes. Callers should pass
 *                    `kFipsKatMaxTableSize` (`0x1F80`, excluding `.chip_info`
 *                    and ECC-poisoned `rom_ctrl` digest words) rather than the
 *                    full ePMP NAPOT window `kFipsKatRegionSize` (`0x2000`).
 * @return Pointer to validated table, or NULL if invalid/absent.
 */
static inline const fips_kat_descriptor_table_t *
get_fips_descriptor_table_from_region(const void *region_base,
                                      size_t region_size) {
  const fips_kat_descriptor_table_t *table =
      (const fips_kat_descriptor_table_t *)region_base;
  if (!validate_fips_descriptor_table(table, region_size)) {
    return NULL;
  }
  return table;
}

/**
 * Searches a validated descriptor table for an entry matching `alg_id`.
 *
 * @param table Pointer to descriptor table.
 * @param region_size Usable table bound in bytes. Callers should pass
 *                    `kFipsKatMaxTableSize` (`0x1F80`, excluding `.chip_info`
 *                    and ECC-poisoned `rom_ctrl` digest words) rather than the
 *                    full ePMP NAPOT window `kFipsKatRegionSize` (`0x2000`).
 * @param alg_id Algorithm identifier to search for.
 * @return Pointer to entry if found, NULL otherwise.
 */
static inline const fips_kat_entry_t *find_fips_entry(
    const fips_kat_descriptor_table_t *table, size_t region_size,
    fips_kat_alg_id_t alg_id) {
  if (alg_id == kFipsKatAlgNone ||
      !validate_fips_descriptor_table(table, region_size)) {
    return NULL;
  }
  const uint32_t entry_count = table->entry_count;
  for (uint32_t i = 0; i < entry_count; ++i) {
    if ((uint32_t)table->entries[i].algorithm_id == (uint32_t)alg_id) {
      return &table->entries[i];
    }
  }
  return NULL;
}

/**
 * Resolves a pointer to the serialized payload for `entry`, enforcing:
 * - Full descriptor table validation against `region_size`,
 * - `entry` is an exact element of `table->entries[0 .. entry_count - 1]`,
 * - `entry->reserved == 0` (defense-in-depth),
 * - 4-byte alignment of `entry->offset` and `entry->size`,
 * - `entry->size > 0`,
 * - No overlap with the table header/entries (`offset >= header_size`),
 * - Strict bounds within `[header_size, total_size)` without integer overflow.
 *
 * @param table Pointer to descriptor table.
 * @param region_size Usable table bound in bytes. Callers should pass
 *                    `kFipsKatMaxTableSize` (`0x1F80`, excluding `.chip_info`
 *                    and ECC-poisoned `rom_ctrl` digest words) rather than the
 *                    full ePMP NAPOT window `kFipsKatRegionSize` (`0x2000`).
 * @param entry Pointer to an entry within `table->entries[]`.
 * @return Pointer to 4-byte aligned data payload, or NULL if invalid.
 */
static inline const void *get_fips_data(
    const fips_kat_descriptor_table_t *table, size_t region_size,
    const fips_kat_entry_t *entry) {
  if (!validate_fips_descriptor_table(table, region_size) || entry == NULL ||
      ((uintptr_t)entry & 0x3u) != 0) {
    return NULL;
  }
  const uint32_t entry_count = table->entry_count;
  const uint32_t total_size = table->total_size;
  const size_t entries_bytes = (size_t)entry_count * sizeof(fips_kat_entry_t);
  const size_t header_size =
      sizeof(fips_kat_descriptor_table_t) + entries_bytes;

  const uintptr_t entries_start = (uintptr_t)&table->entries[0];
  const uintptr_t entry_addr = (uintptr_t)entry;
  if (entry_addr < entries_start ||
      (entry_addr - entries_start) >= entries_bytes ||
      ((entry_addr - entries_start) % sizeof(fips_kat_entry_t)) != 0) {
    return NULL;
  }

  if (entry->reserved != 0) {
    return NULL;
  }

  const uint32_t offset = entry->offset;
  const uint32_t size = entry->size;
  if (size == 0 || (offset & 0x3u) != 0 || (size & 0x3u) != 0) {
    return NULL;
  }
  if ((size_t)offset < header_size || offset >= total_size ||
      size > total_size - offset) {
    return NULL;
  }
  return (const void *)((const uint8_t *)table + offset);
}

/**
 * ============================================================================
 * Uniform 4-Byte Aligned Sub-Field Accessors
 * ============================================================================
 */

// --- hmac_kat_data_t ---
static inline const uint8_t *fips_kat_hmac_key(const hmac_kat_data_t *kat) {
  return kat->data;
}
static inline const uint8_t *fips_kat_hmac_msg(const hmac_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->key_len);
}
static inline const uint8_t *fips_kat_hmac_digest(const hmac_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->key_len) +
         FIPS_KAT_ALIGN4(kat->msg_len);
}
static inline size_t fips_kat_hmac_expected_size(const hmac_kat_data_t *kat) {
  return sizeof(hmac_kat_data_t) + FIPS_KAT_ALIGN4(kat->key_len) +
         FIPS_KAT_ALIGN4(kat->msg_len) + FIPS_KAT_ALIGN4(kat->digest_len);
}

// --- kdf_kat_data_t ---
static inline const uint8_t *fips_kat_kdf_key(const kdf_kat_data_t *kat) {
  return kat->data;
}
static inline const uint8_t *fips_kat_kdf_label(const kdf_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->key_len);
}
static inline const uint8_t *fips_kat_kdf_context(const kdf_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->key_len) +
         FIPS_KAT_ALIGN4(kat->label_len);
}
static inline const uint8_t *fips_kat_kdf_out(const kdf_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->key_len) +
         FIPS_KAT_ALIGN4(kat->label_len) + FIPS_KAT_ALIGN4(kat->context_len);
}
static inline size_t fips_kat_kdf_expected_size(const kdf_kat_data_t *kat) {
  return sizeof(kdf_kat_data_t) + FIPS_KAT_ALIGN4(kat->key_len) +
         FIPS_KAT_ALIGN4(kat->label_len) + FIPS_KAT_ALIGN4(kat->context_len) +
         FIPS_KAT_ALIGN4(kat->out_len);
}

// --- aes_kat_data_t ---
static inline const uint8_t *fips_kat_aes_key(const aes_kat_data_t *kat) {
  return kat->data;
}
static inline const uint8_t *fips_kat_aes_iv(const aes_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->key_len);
}
static inline const uint8_t *fips_kat_aes_aad(const aes_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->key_len) +
         FIPS_KAT_ALIGN4(kat->iv_len);
}
static inline const uint8_t *fips_kat_aes_pt(const aes_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->key_len) +
         FIPS_KAT_ALIGN4(kat->iv_len) + FIPS_KAT_ALIGN4(kat->aad_len);
}
static inline const uint8_t *fips_kat_aes_ct(const aes_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->key_len) +
         FIPS_KAT_ALIGN4(kat->iv_len) + FIPS_KAT_ALIGN4(kat->aad_len) +
         FIPS_KAT_ALIGN4(kat->pt_len);
}
static inline const uint8_t *fips_kat_aes_tag(const aes_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->key_len) +
         FIPS_KAT_ALIGN4(kat->iv_len) + FIPS_KAT_ALIGN4(kat->aad_len) +
         FIPS_KAT_ALIGN4(kat->pt_len) + FIPS_KAT_ALIGN4(kat->ct_len);
}
static inline size_t fips_kat_aes_expected_size(const aes_kat_data_t *kat) {
  return sizeof(aes_kat_data_t) + FIPS_KAT_ALIGN4(kat->key_len) +
         FIPS_KAT_ALIGN4(kat->iv_len) + FIPS_KAT_ALIGN4(kat->aad_len) +
         FIPS_KAT_ALIGN4(kat->pt_len) + FIPS_KAT_ALIGN4(kat->ct_len) +
         FIPS_KAT_ALIGN4(kat->tag_len);
}

// --- asymmetric_verify_kat_data_t ---
static inline const uint8_t *fips_kat_asym_verify_pub_key1(
    const asymmetric_verify_kat_data_t *kat) {
  return kat->data;
}
static inline const uint8_t *fips_kat_asym_verify_pub_key2(
    const asymmetric_verify_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->pub_key_len1);
}
static inline const uint8_t *fips_kat_asym_verify_msg(
    const asymmetric_verify_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->pub_key_len1) +
         FIPS_KAT_ALIGN4(kat->pub_key_len2);
}
static inline const uint8_t *fips_kat_asym_verify_sig1(
    const asymmetric_verify_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->pub_key_len1) +
         FIPS_KAT_ALIGN4(kat->pub_key_len2) + FIPS_KAT_ALIGN4(kat->msg_len);
}
static inline const uint8_t *fips_kat_asym_verify_sig2(
    const asymmetric_verify_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->pub_key_len1) +
         FIPS_KAT_ALIGN4(kat->pub_key_len2) + FIPS_KAT_ALIGN4(kat->msg_len) +
         FIPS_KAT_ALIGN4(kat->sig_len1);
}
static inline size_t fips_kat_asym_verify_expected_size(
    const asymmetric_verify_kat_data_t *kat) {
  return sizeof(asymmetric_verify_kat_data_t) +
         FIPS_KAT_ALIGN4(kat->pub_key_len1) +
         FIPS_KAT_ALIGN4(kat->pub_key_len2) + FIPS_KAT_ALIGN4(kat->msg_len) +
         FIPS_KAT_ALIGN4(kat->sig_len1) + FIPS_KAT_ALIGN4(kat->sig_len2);
}

// --- asymmetric_sign_kat_data_t ---
static inline const uint8_t *fips_kat_asym_sign_priv_key(
    const asymmetric_sign_kat_data_t *kat) {
  return kat->data;
}
static inline const uint8_t *fips_kat_asym_sign_ephemeral(
    const asymmetric_sign_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->priv_key_len);
}
static inline const uint8_t *fips_kat_asym_sign_msg(
    const asymmetric_sign_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->priv_key_len) +
         FIPS_KAT_ALIGN4(kat->ephemeral_len);
}
static inline const uint8_t *fips_kat_asym_sign_sig1(
    const asymmetric_sign_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->priv_key_len) +
         FIPS_KAT_ALIGN4(kat->ephemeral_len) + FIPS_KAT_ALIGN4(kat->msg_len);
}
static inline const uint8_t *fips_kat_asym_sign_sig2(
    const asymmetric_sign_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->priv_key_len) +
         FIPS_KAT_ALIGN4(kat->ephemeral_len) + FIPS_KAT_ALIGN4(kat->msg_len) +
         FIPS_KAT_ALIGN4(kat->sig_len1);
}
static inline size_t fips_kat_asym_sign_expected_size(
    const asymmetric_sign_kat_data_t *kat) {
  return sizeof(asymmetric_sign_kat_data_t) +
         FIPS_KAT_ALIGN4(kat->priv_key_len) +
         FIPS_KAT_ALIGN4(kat->ephemeral_len) + FIPS_KAT_ALIGN4(kat->msg_len) +
         FIPS_KAT_ALIGN4(kat->sig_len1) + FIPS_KAT_ALIGN4(kat->sig_len2);
}

// --- ecdh_kat_data_t ---
static inline const uint8_t *fips_kat_ecdh_priv_key(
    const ecdh_kat_data_t *kat) {
  return kat->data;
}
static inline const uint8_t *fips_kat_ecdh_pub_key1(
    const ecdh_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->priv_key_len);
}
static inline const uint8_t *fips_kat_ecdh_pub_key2(
    const ecdh_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->priv_key_len) +
         FIPS_KAT_ALIGN4(kat->pub_key_len1);
}
static inline const uint8_t *fips_kat_ecdh_shared_secret(
    const ecdh_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->priv_key_len) +
         FIPS_KAT_ALIGN4(kat->pub_key_len1) +
         FIPS_KAT_ALIGN4(kat->pub_key_len2);
}
static inline size_t fips_kat_ecdh_expected_size(const ecdh_kat_data_t *kat) {
  return sizeof(ecdh_kat_data_t) + FIPS_KAT_ALIGN4(kat->priv_key_len) +
         FIPS_KAT_ALIGN4(kat->pub_key_len1) +
         FIPS_KAT_ALIGN4(kat->pub_key_len2) +
         FIPS_KAT_ALIGN4(kat->shared_secret_len);
}

// --- mldsa_kat_data_t ---
static inline size_t fips_kat_mldsa_expected_size(const mldsa_kat_data_t *kat) {
  return sizeof(mldsa_kat_data_t) +
         (size_t)kat->num_cases * sizeof(fips_kat_mldsa87_case_t);
}

// --- kem_kat_data_t ---
static inline const uint8_t *fips_kat_kem_seed_d(const kem_kat_data_t *kat) {
  return kat->data;
}
static inline const uint8_t *fips_kat_kem_seed_z(const kem_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->seed_d_len);
}
static inline const uint8_t *fips_kat_kem_seed_m(const kem_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->seed_d_len) +
         FIPS_KAT_ALIGN4(kat->seed_z_len);
}
static inline const uint8_t *fips_kat_kem_exp_pk_hash(
    const kem_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->seed_d_len) +
         FIPS_KAT_ALIGN4(kat->seed_z_len) + FIPS_KAT_ALIGN4(kat->seed_m_len);
}
static inline const uint8_t *fips_kat_kem_exp_ct_hash(
    const kem_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->seed_d_len) +
         FIPS_KAT_ALIGN4(kat->seed_z_len) + FIPS_KAT_ALIGN4(kat->seed_m_len) +
         FIPS_KAT_ALIGN4(kat->exp_pk_hash_len);
}
static inline const uint8_t *fips_kat_kem_exp_ss(const kem_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->seed_d_len) +
         FIPS_KAT_ALIGN4(kat->seed_z_len) + FIPS_KAT_ALIGN4(kat->seed_m_len) +
         FIPS_KAT_ALIGN4(kat->exp_pk_hash_len) +
         FIPS_KAT_ALIGN4(kat->exp_ct_hash_len);
}
static inline size_t fips_kat_kem_expected_size(const kem_kat_data_t *kat) {
  return sizeof(kem_kat_data_t) + FIPS_KAT_ALIGN4(kat->seed_d_len) +
         FIPS_KAT_ALIGN4(kat->seed_z_len) + FIPS_KAT_ALIGN4(kat->seed_m_len) +
         FIPS_KAT_ALIGN4(kat->exp_pk_hash_len) +
         FIPS_KAT_ALIGN4(kat->exp_ct_hash_len) +
         FIPS_KAT_ALIGN4(kat->exp_ss_len);
}

// --- hkdf_kat_data_t ---
static inline const uint8_t *fips_kat_hkdf_ikm(const hkdf_kat_data_t *kat) {
  return kat->data;
}
static inline const uint8_t *fips_kat_hkdf_salt(const hkdf_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->ikm_len);
}
static inline const uint8_t *fips_kat_hkdf_info(const hkdf_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->ikm_len) +
         FIPS_KAT_ALIGN4(kat->salt_len);
}
static inline const uint8_t *fips_kat_hkdf_prk(const hkdf_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->ikm_len) +
         FIPS_KAT_ALIGN4(kat->salt_len) + FIPS_KAT_ALIGN4(kat->info_len);
}
static inline const uint8_t *fips_kat_hkdf_okm(const hkdf_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->ikm_len) +
         FIPS_KAT_ALIGN4(kat->salt_len) + FIPS_KAT_ALIGN4(kat->info_len) +
         FIPS_KAT_ALIGN4(kat->prk_len);
}
static inline size_t fips_kat_hkdf_expected_size(const hkdf_kat_data_t *kat) {
  return sizeof(hkdf_kat_data_t) + FIPS_KAT_ALIGN4(kat->ikm_len) +
         FIPS_KAT_ALIGN4(kat->salt_len) + FIPS_KAT_ALIGN4(kat->info_len) +
         FIPS_KAT_ALIGN4(kat->prk_len) + FIPS_KAT_ALIGN4(kat->okm_len);
}

// --- sparse_verify_kat_data_t ---
static inline const uint8_t *fips_kat_sparse_verify_pub_key(
    const sparse_verify_kat_data_t *kat) {
  return kat->data;
}
static inline const uint8_t *fips_kat_sparse_verify_msg(
    const sparse_verify_kat_data_t *kat) {
  return kat->data + FIPS_KAT_ALIGN4(kat->pub_key_len);
}
static inline const fips_kat_sparse_chunk_t *fips_kat_sparse_verify_chunks(
    const sparse_verify_kat_data_t *kat) {
  return (const fips_kat_sparse_chunk_t *)(const void *)(kat->data +
                                                         FIPS_KAT_ALIGN4(
                                                             kat->pub_key_len) +
                                                         FIPS_KAT_ALIGN4(
                                                             kat->msg_len));
}
static inline size_t fips_kat_sparse_verify_expected_size(
    const sparse_verify_kat_data_t *kat) {
  return sizeof(sparse_verify_kat_data_t) + FIPS_KAT_ALIGN4(kat->pub_key_len) +
         FIPS_KAT_ALIGN4(kat->msg_len) +
         (size_t)kat->num_chunks * sizeof(fips_kat_sparse_chunk_t);
}

/**
 * Unpacks a fixed-16-byte-chunk sparse-encoded signature from `kat` into
 * `out_sig`.
 *
 * Enforces strict bounds, alignment, `entry_size == expected_size`, zero
 * `chunk->reserved`, 16-byte-aligned offsets, and strictly ascending
 * non-overlapping chunk offsets.
 *
 * @param kat Pointer to 4-byte aligned `sparse_verify_kat_data_t` payload.
 * @param entry_size Byte size of the serialized payload (`entry->size`).
 * @param[out] out_sig Destination buffer for the expanded signature.
 * @param out_sig_len Length of `out_sig` in bytes (must equal `kat->sig_len`).
 * @return True if all chunks were validated and unpacked cleanly; false
 *         otherwise (with `out_sig` zeroed if touched).
 */
OT_WARN_UNUSED_RESULT
static inline bool fips_kat_sparse_sig_unpack(
    const sparse_verify_kat_data_t *kat, size_t entry_size, uint8_t *out_sig,
    size_t out_sig_len) {
  if (kat == NULL || out_sig == NULL || ((uintptr_t)kat & 0x3u) != 0 ||
      entry_size < sizeof(sparse_verify_kat_data_t) || out_sig_len == 0 ||
      out_sig_len != (size_t)kat->sig_len ||
      entry_size != fips_kat_sparse_verify_expected_size(kat)) {
    return false;
  }

  memset(out_sig, 0, out_sig_len);

  const fips_kat_sparse_chunk_t *chunks = fips_kat_sparse_verify_chunks(kat);
  size_t prev_end = 0;

  for (uint32_t i = 0; i < (uint32_t)kat->num_chunks; ++i) {
    const fips_kat_sparse_chunk_t *chunk = &chunks[i];
    if (chunk->reserved != 0) {
      memset(out_sig, 0, out_sig_len);
      return false;
    }
    const size_t chunk_off = chunk->offset;
    if ((chunk_off & (kFipsKatSparseChunkBytes - 1u)) != 0 ||
        chunk_off > out_sig_len ||
        kFipsKatSparseChunkBytes > out_sig_len - chunk_off) {
      memset(out_sig, 0, out_sig_len);
      return false;
    }
    if (i > 0 && chunk_off < prev_end) {
      memset(out_sig, 0, out_sig_len);
      return false;
    }
    memcpy(out_sig + chunk_off, chunk->data, kFipsKatSparseChunkBytes);
    prev_end = chunk_off + kFipsKatSparseChunkBytes;
  }

  return true;
}

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_FIPS_KAT_TABLE_H_
