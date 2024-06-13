// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_KEY_TYPES_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_KEY_TYPES_H_

#include <stdint.h>

#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/lib/sigverify/rsa_key.h"
#include "sw/device/silicon_creator/lib/sigverify/spx_key.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Key types.
 *
 * The life cycle states in which a key can be used depend on its type.
 *
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 3 -n 32 \
 *     -s 1985033815 --language=c
 *
 * Minimum Hamming distance: 15
 * Maximum Hamming distance: 18
 * Minimum Hamming weight: 13
 * Maximum Hamming weight: 16
 */
typedef enum sigverify_key_type {
  /**
   * A key used for manufacturing, testing, and RMA.
   *
   * Keys of this type can be used only in TEST_UNLOCKED* and RMA life cycle
   * states.
   */
  kSigverifyKeyTypeTest = 0x3ff0c819,
  /**
   * A production key.
   *
   * Keys of this type can be used in all operational life cycle states, i.e.
   * states in which CPU execution is enabled.
   */
  kSigverifyKeyTypeProd = 0x43a839ad,
  /**
   * A development key.
   *
   * Keys of this type can be used only in the DEV life cycle state.
   */
  kSigverifyKeyTypeDev = 0x7a01a471,
} sigverify_key_type_t;

/**
 * OTP key state encoding values used in the `ROT_CREATOR_AUTH_STATE` OTP
 * partition.
 *
 * The values are derived from the otp_ctrl encoding algorithm to ensure that
 * the following one-directional transitions are possible:
 * - `kSigVerifyKeyAuthStateBlank` -> `kSigVerifyKeyAuthStateProvisioned`
 * - `kSigVerifyKeyAuthStateProvisioned` -> `kSigVerifyKeyAuthStateRevoked`
 *
 * No other state transitions are supported. An attacker who attempts to change
 * the state of the key from `kSigVerifyKeyAuthStateRevoked` to
 * `kSigVerifyKeyAuthStateProvisioned` will trigger an ECC error in the OTP
 * macro
 */
typedef enum sigverify_key_auth_state {
  /**
   * Represents the state of the key as blank.
   */
  kSigVerifyKeyAuthStateBlank = 0,
  /**
   * Represents the state of the key as enabled.
   *
   * The value is derived from the otp_ctrl encoding algorithm to ensure that
   * transitions from this value to `kSigVerifyKeyAuthStateRevoked` are
   * possible (i.e. the value change does not trigger an ECC error in the OTP
   * macro). See https://github.com/lowRISC/opentitan/pull/21270 for more
   * details.
   *
   * parameter logic [15:0] I0 = 16'b0110_0111_1000_0001; // ECC: 6'b000100
   * parameter logic [15:0] I1 = 16'b1110_1000_1010_0001; // ECC: 6'b100110
   * AuthStEnabled  = { I1,  I0},
   */
  kSigVerifyKeyAuthStateProvisioned = 0xe8a16781,
  /**
   * Represents the state of the key as revoked.
   *
   * The value is derived from the otp_ctrl encoding algorithm to ensure that
   * transitions into this value from `kSigVerifyKeyAuthStateProvisioned` are
   * possible (i.e. the value change does not trigger an ECC error in the OTP
   * macro). See https://github.com/lowRISC/opentitan/pull/21270 for more
   * details.
   *
   * parameter logic [15:0] J0 = 16'b0111_1111_1010_0001; // ECC: 6'b101101
   * parameter logic [15:0] J1 = 16'b1110_1001_1111_0101; // ECC: 6'b101111
   * AuthStDisabled = { J1,  J0}
   */
  kSigVerifyKeyAuthStateRevoked = 0xe9f57fa1,
} sigverify_key_auth_state_t;

/**
 * Common initial sequence of public keys stored in ROM.
 *
 * OpenTitan ROM contains RSA and SPX keys whose definitions share this common
 * initial sequence. This common initial sequence allows us to perform key
 * lookup and validity checks in a generic manner by casting
 * `sigverify_rom_rsa_key_t` or `sigverify_rom_spx_key_t` to this type.
 */
typedef struct sigverify_rom_key_header {
  /**
   * Type of the key.
   */
  sigverify_key_type_t key_type;
  /**
   * ID of the key.
   */
  uint32_t key_id;
} sigverify_rom_key_header_t;

OT_ASSERT_MEMBER_OFFSET(sigverify_rom_key_header_t, key_type, 0);
OT_ASSERT_MEMBER_OFFSET(sigverify_rom_key_header_t, key_id, 4);
OT_ASSERT_SIZE(sigverify_rom_key_header_t, 8);

/**
 * An ECDSA P256 public key stored in ROM.
 *
 * This struct must start with the common initial sequence
 * `sigverify_rom_key_header_t`.
 *
 */
typedef struct sigverify_rom_ecdsa_p256_key_entry {
  /**
   * Type of the key.
   */
  sigverify_key_type_t key_type;
  /**
   * An ECDSA P256 public key.
   */
  ecdsa_p256_public_key_t key;
} sigverify_rom_ecdsa_p256_key_entry_t;
OT_ASSERT_MEMBER_OFFSET(sigverify_rom_ecdsa_p256_key_entry_t, key_type, 0);
OT_ASSERT_MEMBER_OFFSET(sigverify_rom_ecdsa_p256_key_entry_t, key.x[0], 4);
static_assert(offsetof(sigverify_rom_key_header_t, key_type) ==
                  offsetof(sigverify_rom_ecdsa_p256_key_entry_t, key_type),
              "Invalid key_type offset.");
static_assert(offsetof(sigverify_rom_key_header_t, key_id) ==
                  offsetof(sigverify_rom_ecdsa_p256_key_entry_t, key.x[0]),
              "Invalid key_id offset.");

/**
 * Union type to inspect the common initial sequence of ECDSA P256 public keys
 *
 */
typedef union sigverify_rom_ecdsa_p256_key {
  /**
   * Common initial sequence.
   */
  sigverify_rom_key_header_t key_header;
  /**
   * Actual ECDSA P256 public key entry.
   */
  sigverify_rom_ecdsa_p256_key_entry_t entry;
} sigverify_rom_ecdsa_p256_key_t;

static_assert(sizeof(sigverify_rom_ecdsa_p256_key_entry_t) ==
                  sizeof(sigverify_rom_ecdsa_p256_key_t),
              "Size of an ECDSA P256 public key entry must be equal to the "
              "size of a key");

/**
 * An RSA public key stored in ROM.
 *
 * This struct must start with the common initial sequence
 * `sigverify_rom_key_header_t`.
 */
typedef struct sigverify_rom_rsa_key_entry {
  /**
   * Type of the key.
   */
  sigverify_key_type_t key_type;
  /**
   * An RSA public key.
   */
  sigverify_rsa_key_t key;
} sigverify_rom_rsa_key_entry_t;
OT_ASSERT_MEMBER_OFFSET(sigverify_rom_rsa_key_entry_t, key_type, 0);
OT_ASSERT_MEMBER_OFFSET(sigverify_rom_rsa_key_entry_t, key.n.data[0], 4);
static_assert(offsetof(sigverify_rom_key_header_t, key_type) ==
                  offsetof(sigverify_rom_rsa_key_entry_t, key_type),
              "Invalid key_type offset.");
static_assert(offsetof(sigverify_rom_key_header_t, key_id) ==
                  offsetof(sigverify_rom_rsa_key_entry_t, key.n.data[0]),
              "Invalid key_id offset.");

/**
 * Union type to inspect the common initial sequence of RSA public keys stored
 * in ROM.
 */
typedef union sigverify_rom_rsa_key {
  /**
   * Common initial sequence.
   */
  sigverify_rom_key_header_t key_header;
  /**
   * Actual RSA public key entry.
   */
  sigverify_rom_rsa_key_entry_t entry;
} sigverify_rom_rsa_key_t;

static_assert(
    sizeof(sigverify_rom_rsa_key_entry_t) == sizeof(sigverify_rom_rsa_key_t),
    "Size of an RSA public key entry must be equal to the size of a key");

/**
 * An SPX public key stored in ROM.
 *
 * This struct must start with the common initial sequence
 * `sigverify_rom_key_header_t`.
 */
typedef struct sigverify_rom_spx_key_entry {
  /**
   * Type of the key.
   */
  sigverify_key_type_t key_type;
  /**
   * An SPX public key.
   */
  sigverify_spx_key_t key;
  /**
   * Parameter configuration ID for the SPX key.
   */
  sigverify_spx_config_id_t config_id;
} sigverify_rom_spx_key_entry_t;

OT_ASSERT_MEMBER_OFFSET(sigverify_rom_spx_key_entry_t, key_type, 0);
OT_ASSERT_MEMBER_OFFSET(sigverify_rom_spx_key_entry_t, key.data[0], 4);
static_assert(offsetof(sigverify_rom_key_header_t, key_type) ==
                  offsetof(sigverify_rom_spx_key_entry_t, key_type),
              "Invalid key_type offset.");
static_assert(offsetof(sigverify_rom_key_header_t, key_id) ==
                  offsetof(sigverify_rom_spx_key_entry_t, key.data[0]),
              "Invalid key_id offset.");

/**
 * Union type to inspect the common initial sequence of SPX public keys stored
 * in ROM.
 */
typedef union sigverify_rom_spx_key {
  /**
   * Common initial sequence.
   */
  sigverify_rom_key_header_t key_header;
  /**
   * Actual SPX public key entry.
   */
  sigverify_rom_spx_key_entry_t entry;
} sigverify_rom_spx_key_t;

static_assert(
    sizeof(sigverify_rom_spx_key_entry_t) == sizeof(sigverify_rom_spx_key_t),
    "Size of an SPX public key entry must be equal to the size of a key");

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_KEY_TYPES_H_
