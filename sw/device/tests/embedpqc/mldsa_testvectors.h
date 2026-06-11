// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_EMBEDPQC_MLDSA_TESTVECTORS_H_
#define OPENTITAN_SW_DEVICE_TESTS_EMBEDPQC_MLDSA_TESTVECTORS_H_

#include <stdint.h>

#include "third_party/embedpqc/mldsa44_tiny.h"

// ML-DSA-44 vectors
extern const uint8_t kMldsa44KeygenSeed[MLDSA44_PRIVATE_SEED_BYTES];
extern const uint8_t kMldsa44ExpectedPublicKey[MLDSA44_PUBLIC_KEY_BYTES];
extern const uint8_t kMldsa44Message[11];
extern const uint8_t kMldsa44ExpectedSignature[MLDSA44_SIGNATURE_BYTES];

#endif  // OPENTITAN_SW_DEVICE_TESTS_EMBEDPQC_MLDSA_TESTVECTORS_H_
