// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/ecdsa.h"

#include <stdbool.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#ifdef USE_CRYPTOC
// TODO(cfrantz): Replace the CryptoC implementation with a native OpenTitan
// implementation.
#include "sw/vendor/cryptoc/include/cryptoc/p256.h"
#include "sw/vendor/cryptoc/include/cryptoc/p256_ecdsa.h"

// This satisfies cryptoc's use of the assert macro.
OT_WEAK void __assert_func(const char *file, int line, const char *func,
                           const char *expr) {
  while (true) {
    HARDENED_TRAP();
  }
}
#else
#error "No ECDSA implementation for lib/ownership."
#endif

hardened_bool_t ecdsa_verify_digest(const owner_key_t *pubkey,
                                    const owner_signature_t *signature,
                                    const hmac_digest_t *digest) {
#ifdef USE_CRYPTOC
  const p256_int *x = (const p256_int *)&pubkey->key[0];
  const p256_int *y = (const p256_int *)&pubkey->key[8];
  const p256_int *r = (const p256_int *)&signature->signature[0];
  const p256_int *s = (const p256_int *)&signature->signature[8];
  const p256_int *message = (const p256_int *)&digest->digest;

  int ok = p256_ecdsa_verify(x, y, message, r, s);
  hardened_bool_t result = ok ? kHardenedBoolTrue : kHardenedBoolFalse;
  return result;
#endif
}

hardened_bool_t ecdsa_verify_message(const owner_key_t *pubkey,
                                     const owner_signature_t *signature,
                                     const void *message, size_t message_len) {
  hmac_digest_t digest;
  hmac_sha256(message, message_len, &digest);
  return ecdsa_verify_digest(pubkey, signature, &digest);
}
