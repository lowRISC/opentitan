// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/lib/testing/entropy_testutils.h"

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static void setup_entropy_src(const dif_entropy_src_t *entropy_src) {
  CHECK_DIF_OK(dif_entropy_src_configure(
      entropy_src, entropy_testutils_config_default(), kDifToggleEnabled));
}

dif_entropy_src_config_t entropy_testutils_config_default(void) {
  return (dif_entropy_src_config_t){
      .fips_enable = true,
      .route_to_firmware = false,
      .bypass_conditioner = false,
      .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
      .health_test_window_size = 0x0200,
      .alert_threshold = 2,
  };
}

void entropy_testutils_auto_mode_init(void) {
  const dif_entropy_src_t entropy_src = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR)};
  const dif_csrng_t csrng = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR)};
  const dif_edn_t edn0 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR)};
  const dif_edn_t edn1 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR)};

  entropy_testutils_stop_all();

  // re-eanble entropy src and csrng
  setup_entropy_src(&entropy_src);
  CHECK_DIF_OK(dif_csrng_configure(&csrng));

  // Re-enable EDN0 in auto mode.
  const dif_edn_auto_params_t edn0_params = {
      // EDN0 provides lower-quality entropy.  Let one generate command return 8
      // blocks, and reseed every 32 generates.
      .reseed_material =
          {
              .len = 1,
              .data = {0x00000002 |  // Reseed from entropy source only.
                       kMultiBitBool4False << 8},
          },
      .generate_material =
          {
              .len = 1, .data = {0x00008003},  // One generate returns 8 blocks.
          },
      .reseed_interval = 32,  // Reseed every 32 generates.
  };
  CHECK_DIF_OK(dif_edn_set_auto_mode(&edn0, edn0_params));

  // Re-enable EDN1 in auto mode.
  const dif_edn_auto_params_t edn1_params = {
      // EDN1 provides highest-quality entropy.  Let one generate command
      // return 1 block, and reseed after every generate.
      .reseed_material =
          {
              .len = 1,
              .data = {0x00000002 |  // Reseed from entropy source only.
                       kMultiBitBool4False << 8},
          },
      .generate_material =
          {
              .len = 1, .data = {0x00001003},  // One generate returns 1 block.
          },
      .reseed_interval = 4,  // Reseed after every 4 generates.
  };
  CHECK_DIF_OK(dif_edn_set_auto_mode(&edn1, edn1_params));
}

void entropy_testutils_boot_mode_init(void) {
  const dif_entropy_src_t entropy_src = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR)};
  const dif_csrng_t csrng = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR)};
  const dif_edn_t edn0 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR)};
  const dif_edn_t edn1 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR)};

  entropy_testutils_stop_all();

  setup_entropy_src(&entropy_src);
  CHECK_DIF_OK(dif_csrng_configure(&csrng));
  CHECK_DIF_OK(dif_edn_set_boot_mode(&edn0));
  CHECK_DIF_OK(dif_edn_set_boot_mode(&edn1));
  CHECK_DIF_OK(dif_edn_configure(&edn0));
  CHECK_DIF_OK(dif_edn_configure(&edn1));
}

void entropy_testutils_fw_override_enable(dif_entropy_src_t *entropy_src,
                                          uint8_t buffer_threshold,
                                          bool route_to_firmware,
                                          bool bypass_conditioner) {
  const dif_entropy_src_fw_override_config_t fw_override_config = {
      .entropy_insert_enable = true,
      .buffer_threshold = buffer_threshold,
  };
  CHECK_DIF_OK(dif_entropy_src_fw_override_configure(
      entropy_src, fw_override_config, kDifToggleEnabled));

  const dif_entropy_src_config_t config = {
      .fips_enable = true,
      .route_to_firmware = route_to_firmware,
      .bypass_conditioner = bypass_conditioner,
      .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
      .health_test_threshold_scope = false,
      .health_test_window_size = 0x0200,
      .alert_threshold = 2,
  };
  CHECK_DIF_OK(
      dif_entropy_src_configure(entropy_src, config, kDifToggleEnabled));
}

void entropy_testutils_wait_for_state(const dif_entropy_src_t *entropy_src,
                                      dif_entropy_src_main_fsm_t state) {
  dif_entropy_src_main_fsm_t cur_state;

  do {
    CHECK_DIF_OK(dif_entropy_src_get_main_fsm_state(entropy_src, &cur_state));
  } while (cur_state != state);
}

void entropy_testutils_stop_all(void) {
  const dif_entropy_src_t entropy_src = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR)};
  const dif_csrng_t csrng = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR)};
  const dif_edn_t edn0 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR)};
  const dif_edn_t edn1 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR)};

  CHECK_DIF_OK(dif_edn_stop(&edn0));
  CHECK_DIF_OK(dif_edn_stop(&edn1));
  CHECK_DIF_OK(dif_csrng_stop(&csrng));
  CHECK_DIF_OK(dif_entropy_src_stop(&entropy_src));
}
