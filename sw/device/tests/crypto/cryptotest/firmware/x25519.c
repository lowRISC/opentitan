// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_curve25519.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/x25519_commands.h"

// Copied from internal headers to remove dependencies.
// kOtcryptoKeyModeX25519 is typed as kOtcryptoKeyTypeEcc, so the keyblob
// library appends 64 redundant bits per share (see keyblob.c). These extra
// bytes are zero-padded and unused by the X25519 algorithm itself.
enum {
  kX25519PrivateKeyWords = X25519_CMD_PRIVATE_KEY_BYTES / sizeof(uint32_t),
  kX25519MaskedScalarShareBytes = X25519_CMD_PRIVATE_KEY_BYTES + (64 / 8),
  kX25519MaskedScalarShareWords =
      kX25519MaskedScalarShareBytes / sizeof(uint32_t),
  kX25519MaskedScalarTotalWords = 2 * kX25519MaskedScalarShareWords,
  kX25519PublicKeyWords = X25519_CMD_PUBLIC_KEY_BYTES / sizeof(uint32_t),
  kX25519SharedSecretWords = X25519_CMD_SHARED_SECRET_BYTES / sizeof(uint32_t),
};

static const otcrypto_key_config_t kX25519PrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeX25519,
    .key_length = X25519_CMD_PRIVATE_KEY_BYTES,
    .hw_backed = kHardenedBoolFalse,
    .exportable = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

status_t handle_x25519_shared_secret_generation(ujson_t *uj) {
  cryptotest_x25519_private_key_t uj_private_key;
  cryptotest_x25519_public_key_t uj_public_key;

  TRY(ujson_deserialize_cryptotest_x25519_private_key_t(uj, &uj_private_key));
  TRY(ujson_deserialize_cryptotest_x25519_public_key_t(uj, &uj_public_key));

  if (uj_private_key.private_key_len != X25519_CMD_PRIVATE_KEY_BYTES) {
    LOG_ERROR("Invalid X25519 private key length (have = %d, want = %d bytes)",
              (uint32_t)uj_private_key.private_key_len,
              X25519_CMD_PRIVATE_KEY_BYTES);
    return INVALID_ARGUMENT();
  }
  if (uj_public_key.public_key_len != X25519_CMD_PUBLIC_KEY_BYTES) {
    LOG_ERROR("Invalid X25519 public key length (have = %d, want = %d bytes)",
              (uint32_t)uj_public_key.public_key_len,
              X25519_CMD_PUBLIC_KEY_BYTES);
    return INVALID_ARGUMENT();
  }

  // Copy the raw private key into a word-aligned buffer.
  uint32_t raw_key[kX25519PrivateKeyWords] = {0};
  memcpy(raw_key, uj_private_key.private_key, X25519_CMD_PRIVATE_KEY_BYTES);

  // Apply blinding on the device: generate a random share1, then compute
  // share0 = raw_key - share1 (mod 2^256). The extra padding words per share
  // (beyond kX25519PrivateKeyWords) remain zero-initialized.
  uint32_t keyblob[kX25519MaskedScalarTotalWords] = {0};
  uint32_t *share0 = keyblob;
  uint32_t *share1 = keyblob + kX25519MaskedScalarShareWords;
  HARDENED_TRY(hardened_memshred(share1, kX25519PrivateKeyWords));
  HARDENED_TRY(hardened_sub(raw_key, share1, kX25519PrivateKeyWords, share0));

  otcrypto_blinded_key_t private_key = {
      .config = kX25519PrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  private_key.checksum = otcrypto_integrity_blinded_checksum(&private_key);

  // Build the peer's unblinded public key from the raw u-coordinate bytes.
  uint32_t public_key_buf[kX25519PublicKeyWords] = {0};
  memcpy(public_key_buf, uj_public_key.public_key, X25519_CMD_PUBLIC_KEY_BYTES);
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeX25519,
      .key_length = X25519_CMD_PUBLIC_KEY_BYTES,
      .key = public_key_buf,
  };
  public_key.checksum = otcrypto_integrity_unblinded_checksum(&public_key);

  // Allocate the blinded shared secret output (symmetric key, two XOR shares).
  uint32_t shared_secretblob[kX25519SharedSecretWords * 2];
  memset(shared_secretblob, 0, sizeof(shared_secretblob));
  otcrypto_blinded_key_t shared_secret = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeAesCtr,
              .key_length = X25519_CMD_SHARED_SECRET_BYTES,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolTrue,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(shared_secretblob),
      .keyblob = shared_secretblob,
  };

  cryptotest_x25519_derive_output_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  uj_output.shared_secret_len = X25519_CMD_SHARED_SECRET_BYTES;

  otcrypto_status_t status =
      otcrypto_x25519(&private_key, &public_key, &shared_secret);
  switch (status.value) {
    case kOtcryptoStatusValueOk:
      uj_output.result = true;
      break;
    case kOtcryptoStatusValueBadArgs:
      uj_output.result = false;
      RESP_OK(ujson_serialize_cryptotest_x25519_derive_output_t, uj,
              &uj_output);
      return OK_STATUS();
    default:
      TRY(status);
      break;
  }

  // Unmask the shared secret by XOR-ing the two output shares.
  uint32_t dest_share0[kX25519SharedSecretWords];
  uint32_t dest_share1[kX25519SharedSecretWords];
  otcrypto_word32_buf_t share0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, dest_share0, ARRAYSIZE(dest_share0));
  otcrypto_word32_buf_t share1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, dest_share1, ARRAYSIZE(dest_share1));
  TRY(otcrypto_export_blinded_key(&shared_secret, &share0_buf, &share1_buf));

  uint32_t unblinded_secret[kX25519SharedSecretWords];
  TRY(hardened_add(dest_share0, dest_share1, kX25519SharedSecretWords,
                   unblinded_secret));

  memcpy(uj_output.shared_secret, unblinded_secret,
         X25519_CMD_SHARED_SECRET_BYTES);

  RESP_OK(ujson_serialize_cryptotest_x25519_derive_output_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_x25519(ujson_t *uj) {
  x25519_subcommand_t cmd;
  TRY(ujson_deserialize_x25519_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kX25519SubcommandX25519SSG:
      return handle_x25519_shared_secret_generation(uj);
    default:
      LOG_ERROR("Unrecognized X25519 subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
