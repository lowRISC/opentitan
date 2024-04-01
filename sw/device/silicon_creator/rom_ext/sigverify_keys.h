// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_SIGVERIFY_KEYS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_SIGVERIFY_KEYS_H_

#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/rsa_key.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * ROM_EXT Key types.
 *
 * ROM_EXT key types are unlike ROM key types:
 * - ROM key types are bound to certain lifecycle states.  ROM_EXT keys types
 *   are not.
 * - ROM_EXT key types affect keymgr diversification.  This prevents the
 *   different keys types from being able to derive the same secrets.
 *
 * To distinguish these types from ROM key types, we refer to them as firmware
 * keys.
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
   * A testing key.
   */
  kSigverifyKeyTypeFirmwareTest = 0x3ff0c819,
  /**
   * A production key.
   */
  kSigverifyKeyTypeFirmwareProd = 0x43a839ad,
  /**
   * A development key.
   */
  kSigverifyKeyTypeFirmwareDev = 0x7a01a471,
} sigverify_key_type_t;

/**
 * An RSA public key stored in ROM.
 */
typedef struct sigverify_rom_ext_key {
  /**
   * An RSA public key.
   */
  sigverify_rsa_key_t key;
  /**
   * Type of the key.
   */
  sigverify_key_type_t key_type;
} sigverify_rom_ext_key_t;

/**
 * Number of RSA public keys.
 */
extern const size_t kSigverifyRsaKeysCnt;

/**
 * Step size to use when checking RSA public keys.
 *
 * This must be coprime with and less than `kSigverifyNumRsaKeys`.
 * Note: Step size is not applicable when `kSigverifyNumRsaKeys` is 1.
 */
extern const size_t kSigverifyRsaKeysStep;

/**
 * Public keys for signature verification.
 */
extern const sigverify_rom_ext_key_t kSigverifyRsaKeys[];

/**
 * Returns the key with the given ID.
 *
 * This function returns the key only if it can be used in the given life cycle
 * state and is valid in OTP. OTP check is performed only if the device is in a
 * non-test operational state (PROD, PROD_END, DEV, RMA).
 *
 * @param key_id A key ID.
 * @param lc_state Life cycle state of the device.
 * @param key Key with the given ID, valid only if it exists.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sigverify_rsa_key_get(uint32_t key_id,
                                  const sigverify_rsa_key_t **key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_SIGVERIFY_KEYS_H_
