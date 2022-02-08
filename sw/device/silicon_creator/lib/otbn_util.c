// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/otbn_util.h"

#include <assert.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/drivers/otbn.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

void otbn_init(otbn_t *ctx) {
  *ctx = (otbn_t){
      .app = {0},
      .app_is_loaded = kHardenedBoolFalse,
      .error_bits = kOtbnErrBitsNoError,
  };
}

rom_error_t otbn_busy_wait_for_done(otbn_t *ctx) {
  while (otbn_is_busy()) {
  }

  otbn_err_bits_t err_bits;
  otbn_get_err_bits(&err_bits);
  if (err_bits != kOtbnErrBitsNoError) {
    ctx->error_bits = err_bits;
    return kErrorOtbnExecutionFailed;
  }
  return kErrorOk;
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
bool check_app_address_ranges(const otbn_app_t *app) {
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

rom_error_t otbn_load_app(otbn_t *ctx, const otbn_app_t app) {
  if (!check_app_address_ranges(&app)) {
    return kErrorOtbnInvalidArgument;
  }

  const size_t imem_num_words = app.imem_end - app.imem_start;
  const size_t data_num_words = app.dmem_data_end - app.dmem_data_start;

  ctx->app_is_loaded = kHardenedBoolFalse;

  RETURN_IF_ERROR(otbn_imem_write(0, app.imem_start, imem_num_words));

  otbn_zero_dmem();
  if (data_num_words > 0) {
    RETURN_IF_ERROR(otbn_dmem_write(0, app.dmem_data_start, data_num_words));
  }

  ctx->app = app;
  ctx->app_is_loaded = kHardenedBoolTrue;
  return kErrorOk;
}

rom_error_t otbn_execute_app(otbn_t *ctx) {
  if (launder32(ctx->app_is_loaded) != kHardenedBoolTrue) {
    return kErrorOtbnInvalidArgument;
  }
  HARDENED_CHECK_EQ(ctx->app_is_loaded, kHardenedBoolTrue);

  otbn_execute();
  return kErrorOk;
}

rom_error_t otbn_copy_data_to_otbn(otbn_t *ctx, size_t len, const uint32_t *src,
                                   otbn_addr_t dest) {
  RETURN_IF_ERROR(otbn_dmem_write(dest, src, len));

  return kErrorOk;
}

rom_error_t otbn_copy_data_from_otbn(otbn_t *ctx, size_t len_bytes,
                                     otbn_addr_t src, uint32_t *dest) {
  RETURN_IF_ERROR(otbn_dmem_read(src, dest, len_bytes));

  return kErrorOk;
}
