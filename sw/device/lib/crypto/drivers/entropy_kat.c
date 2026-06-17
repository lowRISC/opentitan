// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/lib/crypto/drivers/entropy_kat.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/status.h"

#include "csrng_regs.h"        // Generated
#include "edn_regs.h"          // Generated
#include "entropy_src_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define MODULE_ID MAKE_MODULE_ID('e', 'n', 'k')

enum {
  kBaseCsrng = TOP_EARLGREY_CSRNG_BASE_ADDR,
  kBaseEntropySrc = TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR,
  kBaseEdn0 = TOP_EARLGREY_EDN0_BASE_ADDR,
  kBaseEdn1 = TOP_EARLGREY_EDN1_BASE_ADDR,
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
    return OTCRYPTO_OK;
  }
  return OTCRYPTO_FATAL_ERR;
}

status_t entropy_csrng_kat(void) {
  HARDENED_TRY(entropy_csrng_uninstantiate());

  const entropy_seed_material_t kEntropyInput = {
      .data = {0x73bec010, 0x9262474c, 0x16a30f76, 0x531b51de, 0x2ee494e5,
               0xdfec9db3, 0xcb7a879d, 0x5600419c, 0xca79b0b0, 0xdda33b5c,
               0xa468649e, 0xdf5d73fa},
      .len = 12,
  };
  HARDENED_TRY(entropy_csrng_instantiate(
      /*disable_trng_input=*/kHardenedBoolTrue, &kEntropyInput));

  const entropy_csrng_internal_state_t kExpectedStateInstantiate = {
      .reseed_counter = 0,
      .v = {0x06b8f59e, 0x43c0b2c2, 0x21052502, 0x217b5214},
      .key = {0x941709fd, 0xd8a25860, 0x861aecf3, 0x98a701a1, 0x0eb2c33b,
              0x74c08fad, 0x632d5227, 0x8c52f901},
      .instantiated = true,
      .fips_compliance = false,
  };
  HARDENED_TRY(check_internal_state(&kExpectedStateInstantiate));

  enum {
    kExpectedOutputLen = 16,
  };

  uint32_t got[kExpectedOutputLen];
  HARDENED_TRY(entropy_csrng_generate(/*seed_material=*/NULL, got,
                                      kExpectedOutputLen,
                                      /*fips_check=*/kHardenedBoolFalse));
  HARDENED_TRY(entropy_csrng_generate(/*seed_material=*/NULL, got,
                                      kExpectedOutputLen,
                                      /*fips_check=*/kHardenedBoolFalse));

  const entropy_csrng_internal_state_t kExpectedStateGenerate = {
      .reseed_counter = 2,
      .v = {0xe73e3392, 0x7d2e92b1, 0x1a0bac9d, 0x53c78ac6},

      .key = {0x66d1b85a, 0xc19d4dfd, 0x053b73e3, 0xe9dc0f90, 0x3f015bc8,
              0x4436e5fd, 0x1cccc697, 0x1a1c6e5f},
      .instantiated = true,
      .fips_compliance = false,
  };
  HARDENED_TRY(check_internal_state(&kExpectedStateGenerate));

  // Note that the word order here is reversed compared to the NIST test
  // vectors.
  const uint32_t kExpectedOutput[kExpectedOutputLen] = {
      0xd1c07cd9, 0x5af8a7f1, 0x1012c84c, 0xe48bb8cb, 0x87189e99, 0xd40fccb1,
      0x771c619b, 0xdf82ab22, 0x80b1dc2f, 0x2581f391, 0x64f7ac0c, 0x510494b3,
      0xa43c41b7, 0xdb17514c, 0x87b107ae, 0x793e01c5,
  };
  if (!memcmp(got, kExpectedOutput, sizeof(kExpectedOutput))) {
    return OTCRYPTO_OK;
  }

  return OTCRYPTO_FATAL_ERR;
}

static void csrng_ctrl_restore(uint32_t *old_ctrl) {
  abs_mmio_write32(kBaseCsrng + CSRNG_CTRL_REG_OFFSET, *old_ctrl);
}

OT_WARN_UNUSED_RESULT
static status_t entropy_src_wait_idle(void) {
  uint32_t cycles_to_wait = 100000;
  do {
    uint32_t debug_status =
        abs_mmio_read32(kBaseEntropySrc + ENTROPY_SRC_DEBUG_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(debug_status,
                            ENTROPY_SRC_DEBUG_STATUS_MAIN_SM_IDLE_BIT)) {
      return OTCRYPTO_OK;
    }
    cycles_to_wait--;
  } while (cycles_to_wait > 0);

  return OTCRYPTO_FATAL_ERR;
}

OT_WARN_UNUSED_RESULT
static status_t entropy_src_kat_configure(void) {
  // Clear up EDN/CSRNG/ENTROPY_SRC.
  entropy_complex_stop_all();
  HARDENED_TRY(entropy_src_wait_idle());

  // Configure ENTROPY_SRC for KAT.
  uint32_t conf = bitfield_field32_write(0, ENTROPY_SRC_CONF_FIPS_ENABLE_FIELD,
                                         kMultiBitBool4True);
  conf = bitfield_field32_write(conf, ENTROPY_SRC_CONF_FIPS_FLAG_FIELD,
                                kMultiBitBool4True);
  conf = bitfield_field32_write(conf, ENTROPY_SRC_CONF_RNG_FIPS_FIELD,
                                kMultiBitBool4False);
  conf = bitfield_field32_write(conf, ENTROPY_SRC_CONF_RNG_BIT_ENABLE_FIELD,
                                kMultiBitBool4False);
  conf = bitfield_field32_write(
      conf, ENTROPY_SRC_CONF_ENTROPY_DATA_REG_ENABLE_FIELD, kMultiBitBool4True);
  conf = bitfield_field32_write(conf, ENTROPY_SRC_CONF_THRESHOLD_SCOPE_FIELD,
                                kMultiBitBool4True);
  abs_mmio_write32(kBaseEntropySrc + ENTROPY_SRC_CONF_REG_OFFSET, conf);

  uint32_t entropy_control = bitfield_field32_write(
      0, ENTROPY_SRC_ENTROPY_CONTROL_ES_ROUTE_FIELD, kMultiBitBool4True);
  entropy_control = bitfield_field32_write(
      entropy_control, ENTROPY_SRC_ENTROPY_CONTROL_ES_TYPE_FIELD,
      kMultiBitBool4False);
  abs_mmio_write32(kBaseEntropySrc + ENTROPY_SRC_ENTROPY_CONTROL_REG_OFFSET,
                   entropy_control);

  uint32_t fw_ov_control = bitfield_field32_write(
      0, ENTROPY_SRC_FW_OV_CONTROL_FW_OV_MODE_FIELD, kMultiBitBool4True);
  fw_ov_control = bitfield_field32_write(
      fw_ov_control, ENTROPY_SRC_FW_OV_CONTROL_FW_OV_ENTROPY_INSERT_FIELD,
      kMultiBitBool4True);
  abs_mmio_write32(kBaseEntropySrc + ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET,
                   fw_ov_control);

  // Clear any configuration-related alerts that might have been triggered.
  abs_mmio_write32(kBaseEntropySrc + ENTROPY_SRC_RECOV_ALERT_STS_REG_OFFSET, 0);

  abs_mmio_write32(kBaseEntropySrc + ENTROPY_SRC_MODULE_ENABLE_REG_OFFSET,
                   kMultiBitBool4True);

  return OTCRYPTO_OK;
}

OT_WARN_UNUSED_RESULT
static status_t entropy_src_fifo_write(const uint32_t *data, size_t len) {
  abs_mmio_write32(kBaseEntropySrc + ENTROPY_SRC_FW_OV_SHA3_START_REG_OFFSET,
                   bitfield_field32_write(
                       0, ENTROPY_SRC_FW_OV_SHA3_START_FW_OV_INSERT_START_FIELD,
                       kMultiBitBool4True));

  for (size_t i = 0; i < len; ++i) {
    uint32_t timeout = 100000;
    while (abs_mmio_read32(kBaseEntropySrc +
                           ENTROPY_SRC_FW_OV_WR_FIFO_FULL_REG_OFFSET) &&
           --timeout > 0) {
    }
    if (timeout == 0) {
      return OTCRYPTO_FATAL_ERR;
    }
    abs_mmio_write32(kBaseEntropySrc + ENTROPY_SRC_FW_OV_WR_DATA_REG_OFFSET,
                     data[i]);
  }

  abs_mmio_write32(kBaseEntropySrc + ENTROPY_SRC_FW_OV_SHA3_START_REG_OFFSET,
                   bitfield_field32_write(
                       0, ENTROPY_SRC_FW_OV_SHA3_START_FW_OV_INSERT_START_FIELD,
                       kMultiBitBool4False));

  return OTCRYPTO_OK;
}

OT_WARN_UNUSED_RESULT
static status_t entropy_src_fifo_read(uint32_t *data, size_t len) {
  for (size_t i = 0; i < len; ++i) {
    uint32_t timeout = 1000000;
    while (
        !(abs_mmio_read32(kBaseEntropySrc + ENTROPY_SRC_INTR_STATE_REG_OFFSET) &
          (1U << ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT)) &&
        --timeout > 0) {
    }
    if (timeout == 0) {
      if (data == NULL) {
        break;
      }
      return OTCRYPTO_FATAL_ERR;
    }
    uint32_t val =
        abs_mmio_read32(kBaseEntropySrc + ENTROPY_SRC_ENTROPY_DATA_REG_OFFSET);
    if (data != NULL) {
      data[i] = val;
    }
    abs_mmio_write32(kBaseEntropySrc + ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                     1U << ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT);
  }
  return OTCRYPTO_OK;
}

status_t entropy_src_sha3_conditioning_kat(void) {
  enum {
    kEntropyFifoBufferSize = 12,
  };

  // If the entropy source is already locked, we cannot run the KAT.
  if (abs_mmio_read32(kBaseEntropySrc + ENTROPY_SRC_SW_REGUPD_REG_OFFSET) ==
      0) {
    return OTCRYPTO_OK;
  }

  uint32_t old_csrng_ctrl __attribute__((cleanup(csrng_ctrl_restore))) =
      abs_mmio_read32(kBaseCsrng + CSRNG_CTRL_REG_OFFSET);
  (void)old_csrng_ctrl;

  // Reconfigure ENTROPY_SRC for KAT.
  HARDENED_TRY(entropy_src_kat_configure());

  // Flush SHA3 conditioner.
  uint32_t zeroes[kEntropyFifoBufferSize] = {0};
  HARDENED_TRY(entropy_src_fifo_write(zeroes, kEntropyFifoBufferSize));
  (void)entropy_src_fifo_read(NULL, kEntropyFifoBufferSize);

  // Run the KAT.
  const uint32_t kInputMsg[kEntropyFifoBufferSize] = {
      0xa52a0da9, 0xcae141b2, 0x6d5bab9d, 0x2c3e5cc0, 0x225afc93, 0x5d31a610,
      0x91b7f960, 0x0d566bb3, 0xef35e170, 0x94ba7d8e, 0x534eb741, 0x6b60b0da,
  };
  HARDENED_TRY(entropy_src_fifo_write(kInputMsg, kEntropyFifoBufferSize));

  uint32_t got[kEntropyFifoBufferSize];
  HARDENED_TRY(entropy_src_fifo_read(got, kEntropyFifoBufferSize));

  const uint32_t kExpectedDigest[kEntropyFifoBufferSize] = {
      0x1c88164a, 0x5ff456e1, 0x0845dbdf, 0xbe233f8e, 0x7a5a4c1b, 0x5d31356a,
      0x751cc536, 0x337375f2, 0x85a1ac19, 0x1333abd4, 0xf745fe0f, 0xc5bbf151,
  };

  if (memcmp(got, kExpectedDigest, sizeof(kExpectedDigest)) == 0) {
    abs_mmio_write32(kBaseEntropySrc + ENTROPY_SRC_RECOV_ALERT_STS_REG_OFFSET,
                     0);
    abs_mmio_write32(kBaseEntropySrc + ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET,
                     ENTROPY_SRC_FW_OV_CONTROL_REG_RESVAL);
    return OTCRYPTO_OK;
  }

  return OTCRYPTO_FATAL_ERR;
}
