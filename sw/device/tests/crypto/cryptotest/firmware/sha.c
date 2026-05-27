// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/crypto/include/sha3.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/sha_commands.h"

status_t handle_sha(ujson_t *uj) {
  cryptotest_sha_mode_t uj_mode;
  cryptotest_sha_input_t uj_input;
  TRY(ujson_deserialize_cryptotest_sha_mode_t(uj, &uj_mode));
  TRY(ujson_deserialize_cryptotest_sha_input_t(uj, &uj_input));

  size_t msg_len = uj_input.msg_len;
  uint8_t msg_buf[msg_len];
  memcpy(msg_buf, uj_input.msg, msg_len);
  const otcrypto_const_byte_buf_t msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, msg_buf, msg_len);

  uint32_t msg_digest_data[SHA_CMD_MAX_DIGEST_BYTES / sizeof(uint32_t)];
  size_t digest_len;

  switch (uj_mode) {
    case kCryptotestShaModeSHA2_256: {
      digest_len = 256 / 8;
      otcrypto_hash_digest_t msg_digest = {
          .data = msg_digest_data,
          .len = digest_len / sizeof(uint32_t),
      };
      TRY(otcrypto_sha2_256(&msg, &msg_digest));
      break;
    }
    case kCryptotestShaModeSHA2_384: {
      digest_len = 384 / 8;
      otcrypto_hash_digest_t msg_digest = {
          .data = msg_digest_data,
          .len = digest_len / sizeof(uint32_t),
      };
      TRY(otcrypto_sha2_384(&msg, &msg_digest));
      break;
    }
    case kCryptotestShaModeSHA2_512: {
      digest_len = 512 / 8;
      otcrypto_hash_digest_t msg_digest = {
          .data = msg_digest_data,
          .len = digest_len / sizeof(uint32_t),
      };
      TRY(otcrypto_sha2_512(&msg, &msg_digest));
      break;
    }
    case kCryptotestShaModeSHA3_224: {
      digest_len = 224 / 8;
      otcrypto_hash_digest_t msg_digest = {
          .data = msg_digest_data,
          .len = digest_len / sizeof(uint32_t),
      };
      TRY(otcrypto_sha3_224(&msg, &msg_digest));
      break;
    }
    case kCryptotestShaModeSHA3_256: {
      digest_len = 256 / 8;
      otcrypto_hash_digest_t msg_digest = {
          .data = msg_digest_data,
          .len = digest_len / sizeof(uint32_t),
      };
      TRY(otcrypto_sha3_256(&msg, &msg_digest));
      break;
    }
    case kCryptotestShaModeSHA3_384: {
      digest_len = 384 / 8;
      otcrypto_hash_digest_t msg_digest = {
          .data = msg_digest_data,
          .len = digest_len / sizeof(uint32_t),
      };
      TRY(otcrypto_sha3_384(&msg, &msg_digest));
      break;
    }
    case kCryptotestShaModeSHA3_512: {
      digest_len = 512 / 8;
      otcrypto_hash_digest_t msg_digest = {
          .data = msg_digest_data,
          .len = digest_len / sizeof(uint32_t),
      };
      TRY(otcrypto_sha3_512(&msg, &msg_digest));
      break;
    }
    case kCryptotestShaModeSHAKE_128: {
      digest_len = uj_input.out_len;
      otcrypto_hash_digest_t msg_digest = {
          .data = msg_digest_data,
          .len = digest_len / sizeof(uint32_t),
      };
      TRY(otcrypto_shake128(&msg, &msg_digest));
      break;
    }
    case kCryptotestShaModeSHAKE_256: {
      digest_len = uj_input.out_len;
      otcrypto_hash_digest_t msg_digest = {
          .data = msg_digest_data,
          .len = digest_len / sizeof(uint32_t),
      };
      TRY(otcrypto_shake256(&msg, &msg_digest));
      break;
    }
    default:
      LOG_ERROR("Unrecognized SHA mode: %d", uj_mode);
      return INVALID_ARGUMENT();
  }

  cryptotest_sha_output_t uj_output;
  memset(uj_output.digest, 0, SHA_CMD_MAX_DIGEST_BYTES);
  memcpy(uj_output.digest, msg_digest_data, digest_len);
  uj_output.digest_len = digest_len;
  RESP_OK(ujson_serialize_cryptotest_sha_output_t, uj, &uj_output);

  return OK_STATUS(0);
}
