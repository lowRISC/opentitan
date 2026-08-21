// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_MLDSA_KEY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_MLDSA_KEY_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "third_party/embedpqc/mldsa44_tiny.h"
#include "third_party/embedpqc/mldsa87_tiny.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

// From Table 1 in FIPS 204
typedef enum mldsa_parameter_set {
  kMldsaParameterSet44,
  kMldsaParameterSet65,
  kMldsaParameterSet87,
} mldsa_parameter_set_t;

typedef struct mldsa_44_public_key {
  uint8_t key[MLDSA44_PUBLIC_KEY_BYTES];
} mldsa_44_public_key_t OT_WORD_ALIGNED;

typedef struct mldsa_44_signature {
  uint8_t signature[MLDSA44_SIGNATURE_BYTES];
} mldsa_44_signature_t OT_WORD_ALIGNED;

typedef struct mldsa_87_public_key {
  uint8_t key[MLDSA87_PUBLIC_KEY_BYTES];
} mldsa_87_public_key_t OT_WORD_ALIGNED;

typedef struct mldsa_87_signature {
  uint8_t signature[MLDSA87_SIGNATURE_BYTES];
} mldsa_87_signature_t OT_WORD_ALIGNED;

typedef struct mldsa_public_key {
  mldsa_parameter_set_t param_set;
  union {
    mldsa_44_public_key_t key_44;
    mldsa_87_public_key_t key_87;
  } key;
} mldsa_public_key_t;

typedef struct mldsa_signature {
  mldsa_parameter_set_t param_set;
  union {
    mldsa_44_signature_t signature_44;
    mldsa_87_signature_t signature_87;
  } key;
} mldsa_signature_t;

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_MLDSA_KEY_H_
