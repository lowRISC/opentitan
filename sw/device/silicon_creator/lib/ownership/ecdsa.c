// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/ecdsa.h"

#include <stdbool.h>

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#if USE_OTBN == 1
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#elif USE_CRYPTOC == 1
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

rom_error_t ecdsa_init(void) {
#if USE_OTBN == 1
  return otbn_boot_app_load();
#elif USE_CRYPTOC == 1
  return kErrorOk;
#endif
}

hardened_bool_t ecdsa_verify_digest(
    const sigverify_ecdsa_p256_buffer_t *pubkey,
    const sigverify_ecdsa_p256_buffer_t *signature,
    const hmac_digest_t *digest) {
#if USE_OTBN == 1
  const attestation_public_key_t *key =
      (const attestation_public_key_t *)pubkey->data;
  const attestation_signature_t *sig =
      (const attestation_signature_t *)signature->data;
  uint32_t rr[8];
  rom_error_t error = otbn_boot_sigverify(key, sig, digest, rr);
  if (error != kErrorOk) {
    return kHardenedBoolFalse;
  }
  return hardened_memeq(sig->r, rr, ARRAYSIZE(rr));
#elif USE_CRYPTOC == 1
  const p256_int *x = (const p256_int *)&pubkey->data[0];
  const p256_int *y = (const p256_int *)&pubkey->data[8];
  const p256_int *r = (const p256_int *)&signature->data[0];
  const p256_int *s = (const p256_int *)&signature->data[8];
  const p256_int *message = (const p256_int *)&digest->digest;

  int ok = p256_ecdsa_verify(x, y, message, r, s);
  hardened_bool_t result = ok ? kHardenedBoolTrue : kHardenedBoolFalse;
  return result;
#endif
}

hardened_bool_t ecdsa_verify_message(
    const sigverify_ecdsa_p256_buffer_t *pubkey,
    const sigverify_ecdsa_p256_buffer_t *signature, const void *message,
    size_t message_len) {
  hmac_digest_t digest;
  hmac_sha256(message, message_len, &digest);
  return ecdsa_verify_digest(pubkey, signature, &digest);
}
