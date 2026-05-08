// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SECURITY_CONFIG_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SECURITY_CONFIG_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Check if the chip is in a secure configuration state.
 *
 * Returns OK if the jittery clock, the dummy instructions, and the data
 * independent timing is enabled.
 *
 * @param security_level Security level of the used key.
 * @returns OK when the security check passed.
 */
OT_WARN_UNUSED_RESULT
status_t otcrypto_security_config_check(
    otcrypto_key_security_level_t security_level);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SECURITY_CONFIG_H_
