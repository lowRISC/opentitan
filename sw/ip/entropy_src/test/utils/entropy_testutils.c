// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/ip/entropy_src/test/utils/entropy_testutils.h"

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/ip/csrng/dif/dif_csrng.h"
#include "sw/ip/csrng/dif/shared/dif_csrng_shared.h"
#include "sw/ip/csrng/driver/csrng.h"
#include "sw/ip/edn/dif/dif_edn.h"
#include "sw/ip/edn/driver/edn.h"
#include "sw/ip/entropy_src/driver/entropy_src.h"
#include "sw/lib/sw/device/base/mmio.h"

status_t entropy_testutils_auto_mode_init(void) {
  const dif_csrng_t csrng = {.base_addr =
                                 mmio_region_from_addr(kCsrngBaseAddr[0])};
  const dif_edn_t edn0 = {.base_addr = mmio_region_from_addr(kEdnBaseAddr[0])};
  const dif_edn_t edn1 = {.base_addr = mmio_region_from_addr(kEdnBaseAddr[1])};

  TRY(entropy_testutils_stop_all());

  // re-eanble csrng
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
  const dif_csrng_t csrng = {.base_addr =
                                 mmio_region_from_addr(kCsrngBaseAddr[0])};
  const dif_edn_t edn0 = {.base_addr = mmio_region_from_addr(kEdnBaseAddr[0])};
  const dif_edn_t edn1 = {.base_addr = mmio_region_from_addr(kEdnBaseAddr[1])};

  TRY(entropy_testutils_stop_all());

  TRY(dif_csrng_configure(&csrng));
  TRY(dif_edn_set_boot_mode(&edn0));
  TRY(dif_edn_set_boot_mode(&edn1));
  TRY(dif_edn_configure(&edn0));
  TRY(dif_edn_configure(&edn1));
  return OK_STATUS();
}

status_t entropy_testutils_stop_all(void) {
  const dif_csrng_t csrng = {.base_addr =
                                 mmio_region_from_addr(kCsrngBaseAddr[0])};
  const dif_edn_t edn0 = {.base_addr = mmio_region_from_addr(kEdnBaseAddr[0])};
  const dif_edn_t edn1 = {.base_addr = mmio_region_from_addr(kEdnBaseAddr[1])};

  TRY(dif_edn_stop(&edn0));
  TRY(dif_edn_stop(&edn1));
  TRY(dif_csrng_stop(&csrng));
  return OK_STATUS();
}

status_t entropy_testutils_error_check(const dif_csrng_t *csrng,
                                       const dif_edn_t *edn0,
                                       const dif_edn_t *edn1) {
  uint32_t err_code;
  bool found_error = false;
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
