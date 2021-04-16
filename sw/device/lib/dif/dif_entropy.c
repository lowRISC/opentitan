// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_entropy.h"

#include <stddef.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"

#include "entropy_src_regs.h"  // Generated.

/**
 * Sets the `entropy` source configuration register with the settings
 * derived from `config`.
 */
static void set_config_register(const dif_entropy_t *entropy,
                                const dif_entropy_config_t *config) {
  // TODO: Make this configurable at the API level.
  // TODO: Currently bypass disable cannot be set, as it causes the hw fsm to
  // get stuck
  // uint32_t reg = 0;
  uint32_t reg =
      bitfield_bit32_write(0, ENTROPY_SRC_CONF_BOOT_BYPASS_DISABLE_BIT, 1);

  // Configure test cases
  reg = bitfield_bit32_write(reg, ENTROPY_SRC_CONF_REPCNT_DISABLE_BIT,
                             !config->tests[kDifEntropyTestRepCount]);
  reg = bitfield_bit32_write(reg, ENTROPY_SRC_CONF_ADAPTP_DISABLE_BIT,
                             !config->tests[kDifEntropyTestAdaptiveProportion]);
  reg = bitfield_bit32_write(reg, ENTROPY_SRC_CONF_BUCKET_DISABLE_BIT,
                             !config->tests[kDifEntropyTestBucket]);
  reg = bitfield_bit32_write(reg, ENTROPY_SRC_CONF_MARKOV_DISABLE_BIT,
                             !config->tests[kDifEntropyTestMarkov]);
  reg = bitfield_bit32_write(reg, ENTROPY_SRC_CONF_HEALTH_TEST_CLR_BIT,
                             config->reset_health_test_registers);
  reg = bitfield_bit32_write(reg, ENTROPY_SRC_CONF_EXTHT_ENABLE_BIT, 0);

  // Configure single RNG bit mode
  bool rng_bit_en = config->single_bit_mode != kDifEntropySingleBitModeDisabled;
  reg = bitfield_bit32_write(reg, ENTROPY_SRC_CONF_RNG_BIT_EN_BIT, rng_bit_en);

  uint32_t rng_bit_sel = rng_bit_en ? config->single_bit_mode : 0;
  reg = bitfield_field32_write(reg, ENTROPY_SRC_CONF_RNG_BIT_SEL_FIELD,
                               rng_bit_sel);

  // Enable configuration
  reg =
      bitfield_field32_write(reg, ENTROPY_SRC_CONF_ENABLE_FIELD, config->mode);
  mmio_region_write32(entropy->params.base_addr, ENTROPY_SRC_CONF_REG_OFFSET,
                      reg);
}

dif_entropy_result_t dif_entropy_init(dif_entropy_params_t params,
                                      dif_entropy_t *entropy) {
  if (entropy == NULL) {
    return kDifEntropyBadArg;
  }
  *entropy = (dif_entropy_t){.params = params};
  return kDifEntropyOk;
}

dif_entropy_result_t dif_entropy_configure(const dif_entropy_t *entropy,
                                           dif_entropy_config_t config) {
  if (entropy == NULL) {
    return kDifEntropyBadArg;
  }

  if (config.lfsr_seed > ENTROPY_SRC_SEED_LFSR_SEED_MASK) {
    return kDifEntropyBadArg;
  }

  uint32_t seed = config.mode == kDifEntropyModeLfsr ? config.lfsr_seed : 0;
  mmio_region_write32(entropy->params.base_addr, ENTROPY_SRC_SEED_REG_OFFSET,
                      seed);

  mmio_region_write32(entropy->params.base_addr, ENTROPY_SRC_RATE_REG_OFFSET,
                      (uint32_t)config.sample_rate);

  // Conditioning bypass is hardcoded to enabled. Bypass is not intended as
  // a regular mode of operation.
  uint32_t reg = bitfield_bit32_write(
      0, ENTROPY_SRC_ENTROPY_CONTROL_ES_ROUTE_BIT, config.route_to_firmware);
  reg = bitfield_bit32_write(reg, ENTROPY_SRC_ENTROPY_CONTROL_ES_TYPE_BIT, 0);
  mmio_region_write32(entropy->params.base_addr,
                      ENTROPY_SRC_ENTROPY_CONTROL_REG_OFFSET, reg);

  // TODO: Add test configuration parameters.

  // TODO: Add support for FIFO mode.
  mmio_region_write32(entropy->params.base_addr,
                      ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET, 0);

  set_config_register(entropy, &config);
  return kDifEntropyOk;
}

static bool get_entropy_avail(const dif_entropy_t *entropy) {
  return mmio_region_get_bit32(entropy->params.base_addr,
                               ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                               ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT);
}

dif_entropy_result_t dif_entropy_avail(const dif_entropy_t *entropy) {
  if (entropy == NULL) {
    return kDifEntropyBadArg;
  }

  return get_entropy_avail(entropy) ? kDifEntropyOk
                                    : kDifEntropyDataUnAvailable;
}

dif_entropy_result_t dif_entropy_read(const dif_entropy_t *entropy,
                                      uint32_t *word) {
  if (entropy == NULL || word == NULL) {
    return kDifEntropyBadArg;
  }

  // Check if entropy is available
  if (!get_entropy_avail(entropy)) {
    return kDifEntropyDataUnAvailable;
  }

  *word = mmio_region_read32(entropy->params.base_addr,
                             ENTROPY_SRC_ENTROPY_DATA_REG_OFFSET);

  // clear interrupt state after fetching read
  // if there is still entropy available, the interrupt state will set again
  mmio_region_nonatomic_set_bit32(entropy->params.base_addr,
                                  ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                                  ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT);

  return kDifEntropyOk;
}

dif_entropy_result_t dif_entropy_disable(const dif_entropy_t *entropy) {
  // TODO: should first check if entropy is locked and return error if it is.
  mmio_region_write32(entropy->params.base_addr, ENTROPY_SRC_CONF_REG_OFFSET,
                      0);

  return kDifEntropyOk;
}
