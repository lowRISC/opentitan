// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/lib/util.h"

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hash.h"

status_t manuf_util_hash_lc_transition_token(const uint32_t *raw_token,
                                             size_t token_size_bytes,
                                             uint64_t *hashed_token) {
  crypto_const_byte_buf_t input = {
      .data = (unsigned char *)raw_token,
      .len = token_size_bytes,
  };
  crypto_const_byte_buf_t function_name_string = {
      .data = (unsigned char *)"",
      .len = 0,
  };
  crypto_const_byte_buf_t customization_string = {
      .data = (unsigned char *)"LC_CTRL",
      .len = 7,
  };

  // Create a temporary uint32_t buffer and copy the result from there to the
  // uint64_t buffer.
  // TODO(#16556): this is a workaround to avoid violating strict-aliasing; if
  // we pass -fno-strict-aliasing, then we can cast `hashed_token` to `uint32_t
  // *` instead.
  size_t token_num_words = token_size_bytes / sizeof(uint32_t);
  if (token_size_bytes % sizeof(uint32_t) != 0) {
    token_num_words++;
  }
  uint32_t token_data[token_num_words];
  memset(token_data, 0, sizeof(token_data));
  crypto_word32_buf_t output = {
      .data = token_data,
      .len = token_num_words,
  };

  TRY(otcrypto_xof_cshake(input, kXofCshakeModeCshake128, function_name_string,
                          customization_string, token_size_bytes, &output));
  memcpy(hashed_token, token_data, sizeof(token_data));

  return OK_STATUS();
}
