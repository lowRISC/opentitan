// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/lib/testing/entropy_testutils.h"

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static status_t setup_entropy_src(const dif_entropy_src_t *entropy_src) {
  CHECK_DIF_OK(dif_entropy_src_configure(
      entropy_src, entropy_testutils_config_default(), kDifToggleEnabled));
  return OK_STATUS();
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

status_t entropy_testutils_auto_mode_init(void) {
  const dif_entropy_src_t entropy_src = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR)};
  const dif_csrng_t csrng = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR)};
  const dif_edn_t edn0 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR)};
  const dif_edn_t edn1 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR)};

  TRY(entropy_testutils_stop_all());

  // re-eanble entropy src and csrng
  setup_entropy_src(&entropy_src);
  TRY(dif_csrng_configure(&csrng));

  // Re-enable EDN0 in auto mode.
  TRY(dif_edn_set_auto_mode(
      &edn0,
      (dif_edn_auto_params_t){
          // EDN0 provides lower-quality entropy.  Let one generate command
          // return 8
          // blocks, and reseed every 32 generates.
          .instantiate_cmd =
              {
                  .cmd = csrng_cmd_header_build(kCsrngAppCmdInstantiate,
                                                kDifCsrngEntropySrcToggleEnable,
                                                /*cmd_len=*/0,
                                                /*generate_len=*/0),
                  .seed_material =
                      {
                          .len = 0,
                      },
              },
          .reseed_cmd =
              {
                  .cmd = csrng_cmd_header_build(
                      kCsrngAppCmdReseed, kDifCsrngEntropySrcToggleEnable,
                      /*cmd_len=*/0, /*generate_len=*/0),
                  .seed_material =
                      {
                          .len = 0,
                      },
              },
          .generate_cmd =
              {
                  // Generate 8 128-bit blocks.
                  .cmd = csrng_cmd_header_build(kCsrngAppCmdGenerate,
                                                kDifCsrngEntropySrcToggleEnable,
                                                /*cmd_len=*/0,
                                                /*generate_len=*/8),
                  .seed_material =
                      {
                          .len = 0,
                      },
              },
          // Reseed every 32 generates.
          .reseed_interval = 32,
      }));

  // Re-enable EDN1 in auto mode.
  TRY(dif_edn_set_auto_mode(
      &edn1,
      (dif_edn_auto_params_t){
          // EDN1 provides highest-quality entropy.  Let one generate command
          // return 1 block, and reseed after every generate.
          .instantiate_cmd =
              {
                  .cmd = csrng_cmd_header_build(kCsrngAppCmdInstantiate,
                                                kDifCsrngEntropySrcToggleEnable,
                                                /*cmd_len=*/0,
                                                /*generate_len=*/0),
                  .seed_material =
                      {
                          .len = 0,
                      },
              },
          .reseed_cmd =
              {
                  .cmd = csrng_cmd_header_build(
                      kCsrngAppCmdReseed, kDifCsrngEntropySrcToggleEnable,
                      /*cmd_len=*/0, /*generate_len=*/0),
                  .seed_material =
                      {
                          .len = 0,
                      },
              },
          .generate_cmd =
              {
                  // Generate 1 128-bit block.
                  .cmd = csrng_cmd_header_build(kCsrngAppCmdGenerate,
                                                kDifCsrngEntropySrcToggleEnable,
                                                /*cmd_len=*/0,
                                                /*generate_len=*/1),
                  .seed_material =
                      {
                          .len = 0,
                      },
              },
          // Reseed after every 4 generates.
          .reseed_interval = 4,
      }));
  return OK_STATUS();
}

status_t entropy_testutils_boot_mode_init(void) {
  const dif_entropy_src_t entropy_src = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR)};
  const dif_csrng_t csrng = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR)};
  const dif_edn_t edn0 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR)};
  const dif_edn_t edn1 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR)};

  TRY(entropy_testutils_stop_all());

  setup_entropy_src(&entropy_src);
  TRY(dif_csrng_configure(&csrng));
  TRY(dif_edn_set_boot_mode(&edn0));
  TRY(dif_edn_set_boot_mode(&edn1));
  TRY(dif_edn_configure(&edn0));
  TRY(dif_edn_configure(&edn1));
  return OK_STATUS();
}

status_t entropy_testutils_fw_override_enable(dif_entropy_src_t *entropy_src,
                                              uint8_t buffer_threshold,
                                              bool route_to_firmware,
                                              bool bypass_conditioner) {
  const dif_entropy_src_fw_override_config_t fw_override_config = {
      .entropy_insert_enable = true,
      .buffer_threshold = buffer_threshold,
  };
  TRY(dif_entropy_src_fw_override_configure(entropy_src, fw_override_config,
                                            kDifToggleEnabled));

  const dif_entropy_src_config_t config = {
      .fips_enable = true,
      .route_to_firmware = route_to_firmware,
      .bypass_conditioner = bypass_conditioner,
      .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
      .health_test_threshold_scope = false,
      .health_test_window_size = 0x0200,
      .alert_threshold = 2,
  };
  TRY(dif_entropy_src_configure(entropy_src, config, kDifToggleEnabled));
  return OK_STATUS();
}

status_t entropy_testutils_wait_for_state(const dif_entropy_src_t *entropy_src,
                                          dif_entropy_src_main_fsm_t state) {
  dif_entropy_src_main_fsm_t cur_state;

  do {
    TRY(dif_entropy_src_get_main_fsm_state(entropy_src, &cur_state));
  } while (cur_state != state);
  return OK_STATUS();
}

status_t entropy_testutils_stop_all(void) {
  const dif_entropy_src_t entropy_src = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR)};
  const dif_csrng_t csrng = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR)};
  const dif_edn_t edn0 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR)};
  const dif_edn_t edn1 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR)};

  TRY(dif_edn_stop(&edn0));
  TRY(dif_edn_stop(&edn1));
  TRY(dif_csrng_stop(&csrng));
  TRY(dif_entropy_src_stop(&entropy_src));
  return OK_STATUS();
}

status_t entropy_testutils_error_check(const dif_entropy_src_t *entropy_src,
                                       const dif_csrng_t *csrng,
                                       const dif_edn_t *edn0,
                                       const dif_edn_t *edn1) {
  uint32_t err_code;
  bool found_error = false;
  TRY(dif_entropy_src_get_errors(entropy_src, &err_code));
  if (err_code) {
    found_error = true;
    LOG_ERROR("entropy_src status. err: 0x%x", err_code);
  }

  dif_csrng_cmd_status_t status;
  TRY(dif_csrng_get_cmd_interface_status(csrng, &status));
  if (status.errors) {
    found_error = true;
    LOG_ERROR("csrng error status. err: 0x%x, fifo_err: 0x%x, kind: 0x%x",
              status.errors, status.unhealthy_fifos, status.kind);
  }

  uint32_t fifo_errors;
  TRY(dif_edn_get_errors(edn0, &fifo_errors, &err_code));
  if (err_code || fifo_errors) {
    found_error = true;
    LOG_ERROR("end0 error status. err: 0x%x, fifo_err: 0x%x", err_code,
              fifo_errors);
  }

  TRY(dif_edn_get_errors(edn1, &fifo_errors, &err_code));
  if (err_code || fifo_errors) {
    found_error = true;
    LOG_ERROR("end1 error status. err: 0x%x, fifo_err: 0x%x", err_code,
              fifo_errors);
  }
  TRY_CHECK(!found_error, "entropy_testutils_error_check fail");
  return OK_STATUS();
}
