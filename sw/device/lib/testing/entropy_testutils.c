// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/lib/testing/entropy_testutils.h"

#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/testing/test_framework/check.h"

#ifdef HAS_ENTROPY_SRC
#include "sw/device/lib/dif/dif_entropy_src.h"
#endif

#define MODULE_ID MAKE_MODULE_ID('e', 'n', 'y')

status_t entropy_testutils_entropy_src_init(void) {
#ifdef HAS_ENTROPY_SRC
  dif_entropy_src_t entropy_src;
  CHECK_DIF_OK(dif_entropy_src_init_from_dt(kDtEntropySrc, &entropy_src));
  dif_entropy_src_config_t config = {
      .fips_enable = true,
      .fips_flag = true,
      .rng_fips = true,
      .route_to_firmware = false,
      .bypass_conditioner = false,
      .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
      .health_test_window_size = 0x0200,
      .alert_threshold = 2,
  };
  CHECK_DIF_OK(
      dif_entropy_src_configure(&entropy_src, config, kDifToggleEnabled));
#endif
  return OK_STATUS();
}

status_t entropy_testutils_auto_mode_init(void) {
  dif_csrng_t csrng;
  dif_edn_t edn0;
  dif_edn_t edn1;
  CHECK_DIF_OK(dif_csrng_init_from_dt(kDtCsrng, &csrng));
  CHECK_DIF_OK(dif_edn_init_from_dt(kDtEdn0, &edn0));
  CHECK_DIF_OK(dif_edn_init_from_dt(kDtEdn1, &edn1));

  TRY(entropy_testutils_stop_all());

  // re-enable entropy src and csrng
  TRY(entropy_testutils_entropy_src_init());
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
  dif_csrng_t csrng;
  dif_edn_t edn0;
  dif_edn_t edn1;
  CHECK_DIF_OK(dif_csrng_init_from_dt(kDtCsrng, &csrng));
  CHECK_DIF_OK(dif_edn_init_from_dt(kDtEdn0, &edn0));
  CHECK_DIF_OK(dif_edn_init_from_dt(kDtEdn1, &edn1));

  TRY(entropy_testutils_stop_all());

  TRY(entropy_testutils_entropy_src_init());
  TRY(dif_csrng_configure(&csrng));
  TRY(dif_edn_set_boot_mode(&edn0));
  TRY(dif_edn_set_boot_mode(&edn1));
  TRY(dif_edn_configure(&edn0));
  TRY(dif_edn_configure(&edn1));
  return OK_STATUS();
}

status_t entropy_testutils_stop_csrng_edn(void) {
  dif_csrng_t csrng;
  dif_edn_t edn0;
  dif_edn_t edn1;
  CHECK_DIF_OK(dif_csrng_init_from_dt(kDtCsrng, &csrng));
  CHECK_DIF_OK(dif_edn_init_from_dt(kDtEdn0, &edn0));
  CHECK_DIF_OK(dif_edn_init_from_dt(kDtEdn1, &edn1));

  TRY(dif_edn_stop(&edn0));
  TRY(dif_edn_stop(&edn1));
  TRY(dif_csrng_stop(&csrng));
  return OK_STATUS();
}

status_t entropy_testutils_stop_all(void) {
  CHECK_STATUS_OK(entropy_testutils_stop_csrng_edn());

#ifdef HAS_ENTROPY_SRC
  dif_entropy_src_t entropy_src;
  CHECK_DIF_OK(dif_entropy_src_init_from_dt(kDtEntropySrc, &entropy_src));
  TRY(dif_entropy_src_stop(&entropy_src));
#endif

  return OK_STATUS();
}

status_t entropy_testutils_error_check(const dif_csrng_t *csrng,
                                       const dif_edn_t *edn0,
                                       const dif_edn_t *edn1) {
  uint32_t err_code;
  bool found_error = false;

#ifdef HAS_ENTROPY_SRC
  dif_entropy_src_t entropy_src;
  CHECK_DIF_OK(dif_entropy_src_init_from_dt(kDtEntropySrc, &entropy_src));
  TRY(dif_entropy_src_get_errors(&entropy_src, &err_code));
  if (err_code) {
    found_error = true;
    LOG_ERROR("entropy_src status. err: 0x%x", err_code);
  }
#endif

  dif_csrng_cmd_status_t status;
  TRY(dif_csrng_get_cmd_interface_status(csrng, &status));
  if (status.cmd_sts != kDifCsrngCmdStsSuccess) {
    found_error = true;
    LOG_ERROR("csrng error status. err: 0x%x, kind: 0x%x", status.cmd_sts,
              status.kind);
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
