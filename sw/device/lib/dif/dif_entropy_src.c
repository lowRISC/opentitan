// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_entropy_src.h"

#include <stddef.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"

#include "entropy_src_regs.h"  // Generated.

/**
 * Sets the `entropy` source configuration register with the settings
 * derived from `config`.
 */
static void set_config_register(const dif_entropy_src_t *entropy,
                                const dif_entropy_src_config_t *config) {
  // TODO: Make this configurable at the API level.
  uint32_t reg = bitfield_field32_write(
      0, ENTROPY_SRC_CONF_BOOT_BYPASS_DISABLE_FIELD, 0x5);

  uint32_t health_clr_sel = config->reset_health_test_registers ? 0xa : 0x5;
  reg = bitfield_field32_write(reg, ENTROPY_SRC_CONF_HEALTH_TEST_CLR_FIELD,
                               health_clr_sel);

  // Configure single RNG bit mode
  uint32_t rng_bit_en =
      (config->single_bit_mode == kDifEntropySrcSingleBitModeDisabled) ? 0x5
                                                                       : 0xa;
  reg = bitfield_field32_write(reg, ENTROPY_SRC_CONF_RNG_BIT_ENABLE_FIELD,
                               rng_bit_en);

  uint32_t rng_bit_sel = rng_bit_en ? config->single_bit_mode : 0;
  reg = bitfield_field32_write(reg, ENTROPY_SRC_CONF_RNG_BIT_SEL_FIELD,
                               rng_bit_sel);

  // Configure lfsr
  uint32_t lfsr_sel = config->mode == kDifEntropySrcModeLfsr ? 0xa : 0x5;
  reg =
      bitfield_field32_write(reg, ENTROPY_SRC_CONF_LFSR_ENABLE_FIELD, lfsr_sel);

  // Enable configuration
  uint32_t enable_val = config->mode != kDifEntropySrcModeDisabled ? 0xa : 0x5;
  reg = bitfield_field32_write(reg, ENTROPY_SRC_CONF_ENABLE_FIELD, enable_val);
  mmio_region_write32(entropy->params.base_addr, ENTROPY_SRC_CONF_REG_OFFSET,
                      reg);
}

dif_entropy_src_result_t dif_entropy_src_init(dif_entropy_src_params_t params,
                                              dif_entropy_src_t *entropy) {
  if (entropy == NULL) {
    return kDifEntropySrcBadArg;
  }
  *entropy = (dif_entropy_src_t){.params = params};
  return kDifEntropySrcOk;
}

dif_entropy_src_result_t dif_entropy_src_configure(
    const dif_entropy_src_t *entropy, dif_entropy_src_config_t config) {
  if (entropy == NULL) {
    return kDifEntropySrcBadArg;
  }

  if (config.lfsr_seed > ENTROPY_SRC_SEED_LFSR_SEED_MASK) {
    return kDifEntropySrcBadArg;
  }

  uint32_t seed = config.mode == kDifEntropySrcModeLfsr ? config.lfsr_seed : 0;
  mmio_region_write32(entropy->params.base_addr, ENTROPY_SRC_SEED_REG_OFFSET,
                      seed);

  mmio_region_write32(entropy->params.base_addr, ENTROPY_SRC_RATE_REG_OFFSET,
                      (uint32_t)config.sample_rate);

  // Conditioning bypass is hardcoded to enabled. Bypass is not intended as
  // a regular mode of operation.
  uint32_t es_route_val = config.route_to_firmware ? 0xa : 0x5;
  uint32_t reg = bitfield_field32_write(
      0, ENTROPY_SRC_ENTROPY_CONTROL_ES_ROUTE_FIELD, es_route_val);
  reg = bitfield_field32_write(reg, ENTROPY_SRC_ENTROPY_CONTROL_ES_TYPE_FIELD,
                               0x5);
  mmio_region_write32(entropy->params.base_addr,
                      ENTROPY_SRC_ENTROPY_CONTROL_REG_OFFSET, reg);

  // TODO: Add test configuration parameters.

  // TODO: Add support for FIFO mode.
  mmio_region_write32(entropy->params.base_addr,
                      ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET, 0);

  set_config_register(entropy, &config);
  return kDifEntropySrcOk;
}

static bool get_entropy_avail(const dif_entropy_src_t *entropy) {
  return mmio_region_get_bit32(entropy->params.base_addr,
                               ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                               ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT);
}

dif_entropy_src_result_t dif_entropy_src_avail(
    const dif_entropy_src_t *entropy) {
  if (entropy == NULL) {
    return kDifEntropySrcBadArg;
  }

  return get_entropy_avail(entropy) ? kDifEntropySrcOk
                                    : kDifEntropySrcDataUnAvailable;
}

dif_entropy_src_result_t dif_entropy_src_read(const dif_entropy_src_t *entropy,
                                              uint32_t *word) {
  if (entropy == NULL || word == NULL) {
    return kDifEntropySrcBadArg;
  }

  // Check if entropy is available
  if (!get_entropy_avail(entropy)) {
    return kDifEntropySrcDataUnAvailable;
  }

  *word = mmio_region_read32(entropy->params.base_addr,
                             ENTROPY_SRC_ENTROPY_DATA_REG_OFFSET);

  // clear interrupt state after fetching read
  // if there is still entropy available, the interrupt state will set again
  mmio_region_nonatomic_set_bit32(entropy->params.base_addr,
                                  ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                                  ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT);

  return kDifEntropySrcOk;
}

dif_entropy_src_result_t dif_entropy_src_disable(
    const dif_entropy_src_t *entropy) {
  // TODO: should first check if entropy is locked and return error if it is.
  mmio_region_write32(entropy->params.base_addr, ENTROPY_SRC_CONF_REG_OFFSET,
                      0);

  return kDifEntropySrcOk;
}
