// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SELF_INTEGRITY_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SELF_INTEGRITY_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

// Dummy variable to get the parser of generate_jump_table to integrate this.
typedef int dummy_regex_absorber_t;

/**
 * Check the cryptolib's self-integrity by verifying the hash of its binary
 * blob.
 *
 * @returns Whether the cryptolib's self-integrity check passed.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_integrity_check(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SELF_INTEGRITY_H_
