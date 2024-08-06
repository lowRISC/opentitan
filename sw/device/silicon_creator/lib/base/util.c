// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/base/util.h"

uint32_t util_round_up_to(uint32_t input, uint32_t align_bits) {
  uint32_t mask = (1 << align_bits) - 1;
  return (input + mask) & ~mask;
}

uint32_t util_size_to_words(uint32_t bytes) {
  return util_round_up_to(bytes, 2) / sizeof(uint32_t);
}

void util_reverse_bytes(void *buf, size_t num_bytes) {
  unsigned char temp;
  unsigned char *byte_buf = buf;
  for (size_t i = 0; i < (num_bytes / 2); ++i) {
    temp = byte_buf[i];
    byte_buf[i] = byte_buf[num_bytes - i - 1];
    byte_buf[num_bytes - i - 1] = temp;
  }
}
