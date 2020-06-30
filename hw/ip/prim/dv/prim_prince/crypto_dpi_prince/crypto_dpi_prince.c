// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifdef _cplusplus
extern "C" {
#endif

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "prince_ref.h"
#include "svdpi.h"

extern uint64_t c_dpi_prince_encrypt(uint64_t plaintext, uint64_t key0,
                                     uint64_t key1, int num_half_rounds,
                                     int old_key_schedule) {
  return prince_enc_dec_uint64(plaintext, key0, key1, 0, num_half_rounds,
                               old_key_schedule);
}

extern uint64_t c_dpi_prince_decrypt(const uint64_t ciphertext,
                                     const uint64_t key0, const uint64_t key1,
                                     int num_half_rounds,
                                     int old_key_schedule) {
  return prince_enc_dec_uint64(ciphertext, key0, key1, 1, num_half_rounds,
                               old_key_schedule);
}

#ifdef _cplusplus
}
#endif
