// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_THIRD_PARTY_EMBEDPQC_PORTS_MLDSA44_TINY_CALLER_H_
#define OPENTITAN_THIRD_PARTY_EMBEDPQC_PORTS_MLDSA44_TINY_CALLER_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

void mldsa44_tiny_pub_from_seed_with_stack(uint8_t *out_pk, const uint8_t *seed,
                                           void *stack_top);

void mldsa44_tiny_sign_deterministic_with_stack(uint8_t *sig,
                                                const uint8_t *seed,
                                                const uint8_t *msg,
                                                size_t msg_len,
                                                void *stack_top);

int mldsa44_tiny_verify_with_stack(const uint8_t *pk, const uint8_t *sig,
                                   const uint8_t *msg, size_t msg_len,
                                   void *stack_top);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_THIRD_PARTY_EMBEDPQC_PORTS_MLDSA44_TINY_CALLER_H_
