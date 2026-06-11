// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "third_party/embedpqc/ports/shake.h"

#include <string.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"

static void shake_squeeze_generic(uint8_t *out, size_t out_len,
                                  size_t rate_words) {
  if (!kmac_is_squeezing()) {
    kmac_shake256_squeeze_start();
  }

  size_t out_words = out_len / 4;
  if (kmac_squeeze_words((uint32_t *)out, out_words, rate_words) != kErrorOk) {
    HARDENED_TRAP();
  }
}

void SHAKE128_init(shake128_ctxt_t *ctxt) {
  (void)ctxt;
  if (kmac_shake128_configure() != kErrorOk) {
    HARDENED_TRAP();
  }
  if (kmac_shake256_start() != kErrorOk) {
    HARDENED_TRAP();
  }
}

void SHAKE128_absorb(shake128_ctxt_t *ctxt, const uint8_t *in, size_t in_len) {
  (void)ctxt;
  kmac_shake256_absorb(in, in_len);
}

void SHAKE128_squeeze(shake128_ctxt_t *ctxt, uint8_t *out, size_t out_len) {
  (void)ctxt;
  shake_squeeze_generic(out, out_len, 42);
}

void SHAKE128_free(shake128_ctxt_t *ctxt) {
  (void)ctxt;
  if (kmac_done() != kErrorOk) {
    HARDENED_TRAP();
  }
}

void SHAKE256_init(shake256_ctxt_t *ctxt) {
  (void)ctxt;
  if (kmac_shake256_configure() != kErrorOk) {
    HARDENED_TRAP();
  }
  if (kmac_shake256_start() != kErrorOk) {
    HARDENED_TRAP();
  }
}

void SHAKE256_absorb(shake256_ctxt_t *ctxt, const uint8_t *in, size_t in_len) {
  (void)ctxt;
  kmac_shake256_absorb(in, in_len);
}

void SHAKE256_squeeze(shake256_ctxt_t *ctxt, uint8_t *out, size_t out_len) {
  (void)ctxt;
  shake_squeeze_generic(out, out_len, 34);
}

void SHAKE256_free(shake256_ctxt_t *ctxt) {
  (void)ctxt;
  if (kmac_done() != kErrorOk) {
    HARDENED_TRAP();
  }
}

void SHAKE256_buffer(uint8_t *out, size_t out_len, const uint8_t *in,
                     size_t in_len) {
  shake256_ctxt_t ctxt;
  SHAKE256_init(&ctxt);
  SHAKE256_absorb(&ctxt, in, in_len);
  SHAKE256_squeeze(&ctxt, out, out_len);
  SHAKE256_free(&ctxt);
}
