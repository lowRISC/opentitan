// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/otbn_util.h"

#include <assert.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/silicon_creator/lib/base/abs_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/otbn.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

void otbn_init(otbn_t *ctx) {
  *ctx = (otbn_t){
      .app = {0},
      .app_is_loaded = false,
      .error_bits = kOtbnErrBitsNoError,
  };
}

rom_error_t otbn_data_ptr_to_dmem_addr(const otbn_t *ctx, otbn_ptr_t ptr,
                                       uint32_t *dmem_addr_otbn) {
  if (ptr < ctx->app.dmem_start || ptr > ctx->app.dmem_end) {
    return kErrorOtbnInvalidArgument;
  }
  *dmem_addr_otbn = (uintptr_t)ptr - (uintptr_t)ctx->app.dmem_start;
  return kErrorOk;
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

rom_error_t otbn_load_app(otbn_t *ctx, const otbn_app_t app) {
  if (app.imem_end <= app.imem_start || app.dmem_end < app.dmem_start) {
    return kErrorOtbnInvalidArgument;
  }

  const size_t imem_num_words = app.imem_end - app.imem_start;
  const size_t dmem_num_words = app.dmem_end - app.dmem_start;

  ctx->app_is_loaded = false;

  RETURN_IF_ERROR(otbn_imem_write(0, app.imem_start, imem_num_words));

  otbn_zero_dmem();
  if (dmem_num_words > 0) {
    RETURN_IF_ERROR(otbn_dmem_write(0, app.dmem_start, dmem_num_words));
  }

  ctx->app = app;
  ctx->app_is_loaded = true;
  return kErrorOk;
}

rom_error_t otbn_execute_app(otbn_t *ctx) {
  if (!ctx->app_is_loaded) {
    return kErrorOtbnInvalidArgument;
  }

  return otbn_execute();
}

rom_error_t otbn_copy_data_to_otbn(otbn_t *ctx, size_t len, const uint32_t *src,
                                   otbn_ptr_t dest) {
  uint32_t dest_dmem_addr;
  RETURN_IF_ERROR(otbn_data_ptr_to_dmem_addr(ctx, dest, &dest_dmem_addr));
  RETURN_IF_ERROR(otbn_dmem_write(dest_dmem_addr, src, len));

  return kErrorOk;
}

rom_error_t otbn_copy_data_from_otbn(otbn_t *ctx, size_t len_bytes,
                                     otbn_ptr_t src, uint32_t *dest) {
  uint32_t src_dmem_addr;
  RETURN_IF_ERROR(otbn_data_ptr_to_dmem_addr(ctx, src, &src_dmem_addr));
  RETURN_IF_ERROR(otbn_dmem_read(src_dmem_addr, dest, len_bytes));

  return kErrorOk;
}
