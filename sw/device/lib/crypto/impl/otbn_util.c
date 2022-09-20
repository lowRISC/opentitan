// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/otbn_util.h"

#include "sw/device/lib/crypto/drivers/otbn.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

void otbn_init(otbn_t *ctx) {
  *ctx = (otbn_t){
      .app = {0},
      .app_is_loaded = kHardenedBoolFalse,
      .error_bits = kOtbnErrBitsNoError,
  };
}

/**
 * Checks if the OTBN application's IMEM and DMEM address parameters are valid.
 *
 * IMEM and DMEM ranges must not be "backwards" in memory, with the end address
 * coming before the start address, and the IMEM range must additionally be
 * non-empty. Finally, separate sections in DMEM must not overlap each other
 * when converted to DMEM address space.
 *
 * @param app the OTBN application to check
 * @return true if the addresses are valid, otherwise false.
 */
static bool check_app_address_ranges(const otbn_app_t *app) {
  // IMEM must have a strictly positive range (cannot be backwards or empty)
  if (app->imem_end <= app->imem_start) {
    return false;
  }
  // DMEM data section must not be backwards
  if (app->dmem_data_end < app->dmem_data_start) {
    return false;
  }
  return true;
}

otbn_error_t otbn_load_app(otbn_t *ctx, const otbn_app_t app) {
  if (!check_app_address_ranges(&app)) {
    return kOtbnErrorInvalidArgument;
  }

  // Ensure OTBN is idle.
  OTBN_RETURN_IF_ERROR(otbn_assert_idle());

  const size_t imem_num_words = app.imem_end - app.imem_start;
  const size_t data_num_words = app.dmem_data_end - app.dmem_data_start;

  ctx->app_is_loaded = kHardenedBoolFalse;

  OTBN_RETURN_IF_ERROR(otbn_imem_sec_wipe());
  OTBN_RETURN_IF_ERROR(otbn_imem_write(0, app.imem_start, imem_num_words));

  OTBN_RETURN_IF_ERROR(otbn_dmem_sec_wipe());
  if (data_num_words > 0) {
    OTBN_RETURN_IF_ERROR(
        otbn_dmem_write(0, app.dmem_data_start, data_num_words));
  }

  ctx->app = app;
  ctx->app_is_loaded = kHardenedBoolTrue;
  return kOtbnErrorOk;
}

otbn_error_t otbn_execute_app(otbn_t *ctx) {
  if (launder32(ctx->app_is_loaded) != kHardenedBoolTrue) {
    return kOtbnErrorInvalidArgument;
  }
  HARDENED_CHECK_EQ(ctx->app_is_loaded, kHardenedBoolTrue);

  return otbn_execute();
}

otbn_error_t otbn_copy_data_to_otbn(otbn_t *ctx, size_t len,
                                    const uint32_t *src, otbn_addr_t dest) {
  return otbn_dmem_write(dest, src, len);
}

otbn_error_t otbn_copy_data_from_otbn(otbn_t *ctx, size_t len_bytes,
                                      otbn_addr_t src, uint32_t *dest) {
  return otbn_dmem_read(src, dest, len_bytes);
}
