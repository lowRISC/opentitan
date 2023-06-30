// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/lib/crypto/drivers/entropy_kat.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/runtime/log.h"

#include "csrng_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define MODULE_ID MAKE_MODULE_ID('e', 'n', 'k')

enum {
  kBaseCsrng = TOP_EARLGREY_CSRNG_BASE_ADDR,
};

/**
 * CSRNG internal state selector ID.
 */
typedef enum entropy_csrng_internal_state_id {
  /**
   * CSRNG instance assigned to Entropy Distribution Network (EDN) 0.
   */
  kCsrngInternalStateIdEdn0 = 0,
  /**
   * CSRNG instance assigned to Entropy Distribution Network (EDN) 1.
   */
  kCsrngInternalStateIdEdn1 = 1,
  /**
   * CSRNG instance assigned to software interface.
   */
  kCsrngInternalStateIdSw = 2,
} entropy_csrng_internal_state_id_t;

/**
 * CSRNG internal state.
 */
typedef struct entropy_csrng_internal_state {
  /**
   * Indicates the number of requests for pseudorandom bits since instantiation
   * or reseeding.
   */
  uint32_t reseed_counter;
  /**
   * Internal V working state with a 128bit block size.
   */
  uint32_t v[4];
  /**
   * Internal key used to configure the internal CSRNG cipher.
   */
  uint32_t key[8];
  /**
   * Set to true when the CSRNG instance has been instantiated.
   */
  bool instantiated;
  /**
   * Set to true when FIPS compliant entropy was provided directly by the
   * entropy source to instantiate or reseed the CSRNG instance.
   */
  bool fips_compliance;
} entropy_csrng_internal_state_t;

static void entropy_csrng_internal_state_get(
    entropy_csrng_internal_state_id_t instance_id,
    entropy_csrng_internal_state_t *state) {
  // Select the instance id to read the internal state from, request a state
  // machine halt, and wait for the internal registers to be ready to be read.
  uint32_t reg = bitfield_field32_write(
      0, CSRNG_INT_STATE_NUM_INT_STATE_NUM_FIELD, instance_id);
  abs_mmio_write32(kBaseCsrng + CSRNG_INT_STATE_NUM_REG_OFFSET, reg);

  // Read the internal state.
  state->reseed_counter =
      abs_mmio_read32(kBaseCsrng + CSRNG_INT_STATE_VAL_REG_OFFSET);

  for (size_t i = 0; i < ARRAYSIZE(state->v); ++i) {
    state->v[i] = abs_mmio_read32(kBaseCsrng + CSRNG_INT_STATE_VAL_REG_OFFSET);
  }

  for (size_t i = 0; i < ARRAYSIZE(state->key); ++i) {
    state->key[i] =
        abs_mmio_read32(kBaseCsrng + CSRNG_INT_STATE_VAL_REG_OFFSET);
  }

  uint32_t flags = abs_mmio_read32(kBaseCsrng + CSRNG_INT_STATE_VAL_REG_OFFSET);

  // The following bit indexes are defined in
  // https://docs.opentitan.org/hw/ip/csrng/doc/#working-state-values
  state->instantiated = bitfield_bit32_read(flags, /*bit_index=*/0u);
  state->fips_compliance = bitfield_bit32_read(flags, /*bit_index=*/1u);
}

/**
 * Checks the CSRNG internal state against `expected` values.
 *
 * @param csrng A CSRNG handle.
 * @param expected Expected CSRNG internal state.
 */
static status_t check_internal_state(
    const entropy_csrng_internal_state_t *expected) {
  entropy_csrng_internal_state_t got = {0};
  entropy_csrng_internal_state_get(kCsrngInternalStateIdSw, &got);
  if (memcmp(&got, expected, sizeof(entropy_csrng_internal_state_t)) == 0) {
    return OK_STATUS();
  }
  return INTERNAL();
}

status_t entropy_csrng_kat(void) {
  TRY(entropy_csrng_uninstantiate());

  const entropy_seed_material_t kEntropyInput = {
      .data = {0x73bec010, 0x9262474c, 0x16a30f76, 0x531b51de, 0x2ee494e5,
               0xdfec9db3, 0xcb7a879d, 0x5600419c, 0xca79b0b0, 0xdda33b5c,
               0xa468649e, 0xdf5d73fa},
      .len = 12,
  };
  TRY(entropy_csrng_instantiate(
      /*disable_trng_input=*/kHardenedBoolTrue, &kEntropyInput));

  const entropy_csrng_internal_state_t kExpectedStateInstantiate = {
      .reseed_counter = 1,
      .v = {0x06b8f59e, 0x43c0b2c2, 0x21052502, 0x217b5214},
      .key = {0x941709fd, 0xd8a25860, 0x861aecf3, 0x98a701a1, 0x0eb2c33b,
              0x74c08fad, 0x632d5227, 0x8c52f901},
      .instantiated = true,
      .fips_compliance = false,
  };
  TRY(check_internal_state(&kExpectedStateInstantiate));

  enum {
    kExpectedOutputLen = 16,
  };

  uint32_t got[kExpectedOutputLen];
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, got, kExpectedOutputLen));
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, got, kExpectedOutputLen));

  const entropy_csrng_internal_state_t kExpectedStateGenerate = {
      .reseed_counter = 3,
      .v = {0xe73e3392, 0x7d2e92b1, 0x1a0bac9d, 0x53c78ac6},

      .key = {0x66d1b85a, 0xc19d4dfd, 0x053b73e3, 0xe9dc0f90, 0x3f015bc8,
              0x4436e5fd, 0x1cccc697, 0x1a1c6e5f},
      .instantiated = true,
      .fips_compliance = false,
  };
  TRY(check_internal_state(&kExpectedStateGenerate));

  // TODO(#13342): csrng does not provide a linear output order. For example,
  // note the test vector output word order: 12,13,14,15 8,9,10,11 4,5,6,7
  // 0,1,2,3.
  const uint32_t kExpectedOutput[kExpectedOutputLen] = {
      0xe48bb8cb, 0x1012c84c, 0x5af8a7f1, 0xd1c07cd9, 0xdf82ab22, 0x771c619b,
      0xd40fccb1, 0x87189e99, 0x510494b3, 0x64f7ac0c, 0x2581f391, 0x80b1dc2f,
      0x793e01c5, 0x87b107ae, 0xdb17514c, 0xa43c41b7,
  };
  if (!memcmp(got, kExpectedOutput, sizeof(kExpectedOutput))) {
    return OK_STATUS();
  }

  return INTERNAL();
}
