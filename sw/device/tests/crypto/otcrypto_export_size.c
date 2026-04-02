// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/otcrypto_interface.h"

// Simple main function so the linker doesn't discard the inerface struct.
int main(void) {
  uint32_t digest_data[8];
  otcrypto_hash_digest_t digest = {.data = digest_data, .len = 8};
  otcrypto.sha2_256((otcrypto_const_byte_buf_t){.data = NULL, .len = 0},
                    &digest);

  // SHA256('') is a constant value; this will always be 0.
  return digest_data[0] & 1;
}
