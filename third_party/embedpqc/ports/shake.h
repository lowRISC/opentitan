// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_THIRD_PARTY_EMBEDPQC_PORTS_SHAKE_H_
#define OPENTITAN_THIRD_PARTY_EMBEDPQC_PORTS_SHAKE_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

// Stateless dummy contexts for OpenTitan hardware KMAC integration.
typedef struct {
  char dummy;
} shake128_ctxt_t;

typedef struct {
  char dummy;
} shake256_ctxt_t;

void SHAKE128_init(shake128_ctxt_t *ctxt);
void SHAKE128_absorb(shake128_ctxt_t *ctxt, const uint8_t *in, size_t in_len);
void SHAKE128_squeeze(shake128_ctxt_t *ctxt, uint8_t *out, size_t out_len);
void SHAKE128_free(shake128_ctxt_t *ctxt);

void SHAKE256_init(shake256_ctxt_t *ctxt);
void SHAKE256_absorb(shake256_ctxt_t *ctxt, const uint8_t *in, size_t in_len);
void SHAKE256_squeeze(shake256_ctxt_t *ctxt, uint8_t *out, size_t out_len);
void SHAKE256_free(shake256_ctxt_t *ctxt);
void SHAKE256_buffer(uint8_t *out, size_t out_len, const uint8_t *in,
                     size_t in_len);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_THIRD_PARTY_EMBEDPQC_PORTS_SHAKE_H_
