// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/mlkem.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/mlkem/mlkem.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/integrity.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('m', 'k', 'm')

otcrypto_status_t otcrypto_mlkem1024_keygen(
    otcrypto_unblinded_key_t *public_key, otcrypto_blinded_key_t *secret_key) {
  HARDENED_TRY(otcrypto_mlkem1024_keygen_async_start());
  HARDENED_TRY(
      otcrypto_mlkem1024_keygen_async_finalize(public_key, secret_key));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_mlkem1024_encaps(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_word32_buf_t *m, otcrypto_word32_buf_t *ciphertext,
    otcrypto_blinded_key_t *shared_secret) {
  HARDENED_TRY(otcrypto_mlkem1024_encaps_async_start(public_key, m));
  HARDENED_TRY(
      otcrypto_mlkem1024_encaps_async_finalize(ciphertext, shared_secret));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_mlkem1024_decaps(
    const otcrypto_blinded_key_t *secret_key,
    const otcrypto_const_word32_buf_t *ciphertext,
    otcrypto_blinded_key_t *shared_secret) {
  HARDENED_TRY(otcrypto_mlkem1024_decaps_async_start(secret_key, ciphertext));
  HARDENED_TRY(otcrypto_mlkem1024_decaps_async_finalize(shared_secret));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_mlkem1024_keygen_async_start(void) {
  HARDENED_TRY_WIPE_DMEM(mlkem1024_keygen_internal_start());

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_mlkem1024_keygen_async_finalize(
    otcrypto_unblinded_key_t *public_key, otcrypto_blinded_key_t *secret_key) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (public_key == NULL || public_key->key == NULL || secret_key == NULL ||
      secret_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  HARDENED_TRY_WIPE_DMEM(
      mlkem1024_keygen_internal_finalize(public_key, secret_key));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_mlkem1024_encaps_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_word32_buf_t *m) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (public_key == NULL || public_key->key == NULL || m == NULL ||
      m->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  HARDENED_TRY_WIPE_DMEM(mlkem1024_encaps_start(public_key, m));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_mlkem1024_encaps_async_finalize(
    otcrypto_word32_buf_t *ciphertext, otcrypto_blinded_key_t *shared_secret) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ciphertext == NULL || ciphertext->data == NULL || shared_secret == NULL ||
      shared_secret->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  HARDENED_TRY_WIPE_DMEM(mlkem1024_encaps_finalize(ciphertext, shared_secret));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_mlkem1024_decaps_async_start(
    const otcrypto_blinded_key_t *secret_key,
    const otcrypto_const_word32_buf_t *ciphertext) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (secret_key == NULL || secret_key->keyblob == NULL || ciphertext == NULL ||
      ciphertext->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  HARDENED_TRY_WIPE_DMEM(mlkem1024_decaps_start(secret_key, ciphertext));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_mlkem1024_decaps_async_finalize(
    otcrypto_blinded_key_t *shared_secret) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (shared_secret == NULL || shared_secret->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  HARDENED_TRY_WIPE_DMEM(mlkem1024_decaps_finalize(shared_secret));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}
