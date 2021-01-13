// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/otbn.h"

#include "sw/device/lib/dif/dif_otbn.h"

/**
 * Gets the address in OTBN instruction memory referenced by `ptr`.
 *
 * @param ctx The context object.
 * @param ptr The pointer to convert.
 * @param[out] func_addr_otbn The address of the function in OTBN's instruction
 *                            memory.
 * @return The result of the operation; #kOtbnBadArg if `ptr` is not in the
 *         instruction memory space of the currently loaded application.
 */
static otbn_result_t func_ptr_to_otbn_imem_addr(const otbn_t *ctx,
                                                otbn_ptr_t ptr,
                                                uint32_t *imem_addr_otbn) {
  uintptr_t ptr_addr = (uintptr_t)ptr;
  uintptr_t app_imem_start_addr = (uintptr_t)ctx->app.imem_start;
  uintptr_t app_imem_end_addr = (uintptr_t)ctx->app.imem_end;

  if (imem_addr_otbn == NULL || ptr == NULL || ctx == NULL ||
      ptr_addr < app_imem_start_addr || ptr_addr > app_imem_end_addr) {
    return kOtbnBadArg;
  }
  *imem_addr_otbn = ptr_addr - app_imem_start_addr;
  return kOtbnOk;
}

/**
 * Gets the address in OTBN data memory referenced by `ptr`.
 *
 * @param ctx The context object.
 * @param ptr The pointer to convert.
 * @param[out] data_addr_otbn The address of the data in OTBN's data memory.
 * @return The result of the operation; #kOtbnBadArg if `ptr` is not in the data
 *         memory space of the currently loaded application.
 */
static otbn_result_t data_ptr_to_otbn_dmem_addr(const otbn_t *ctx,
                                                otbn_ptr_t ptr,
                                                uint32_t *dmem_addr_otbn) {
  uintptr_t ptr_addr = (uintptr_t)ptr;
  uintptr_t app_dmem_start_addr = (uintptr_t)ctx->app.dmem_start;
  uintptr_t app_dmem_end_addr = (uintptr_t)ctx->app.dmem_end;

  if (dmem_addr_otbn == NULL || ptr == NULL || ctx == NULL ||
      ptr_addr < app_dmem_start_addr || ptr_addr > app_dmem_end_addr) {
    return kOtbnBadArg;
  }
  *dmem_addr_otbn = ptr_addr - app_dmem_start_addr;
  return kOtbnOk;
}

otbn_result_t otbn_busy_wait_for_done(otbn_t *ctx) {
  bool busy = true;
  while (busy) {
    if (dif_otbn_is_busy(&ctx->dif, &busy) != kDifOtbnOk) {
      return kOtbnError;
    }
  }

  dif_otbn_err_bits_t err_bits;
  if (dif_otbn_get_err_bits(&ctx->dif, &err_bits) != kDifOtbnOk) {
    return kOtbnError;
  }
  if (err_bits != kDifOtbnErrBitsNoError) {
    return kOtbnExecutionFailed;
  }
  return kOtbnOk;
}

otbn_result_t otbn_init(otbn_t *ctx, const dif_otbn_config_t dif_config) {
  if (ctx == NULL) {
    return kOtbnBadArg;
  }

  ctx->app_is_loaded = false;

  if (dif_otbn_init(&dif_config, &ctx->dif) != kDifOtbnOk) {
    return kOtbnError;
  }

  return kOtbnOk;
}

otbn_result_t otbn_load_app(otbn_t *ctx, const otbn_app_t app) {
  if (app.imem_end <= app.imem_start || app.dmem_end < app.dmem_start) {
    return kOtbnBadArg;
  }

  const size_t imem_size = app.imem_end - app.imem_start;
  const size_t dmem_size = app.dmem_end - app.dmem_start;

  // Instruction and data memory images must be multiples of 32b words.
  if (imem_size % sizeof(uint32_t) != 0 || dmem_size % sizeof(uint32_t) != 0) {
    return kOtbnBadArg;
  }

  ctx->app_is_loaded = false;
  ctx->app = app;

  if (dif_otbn_imem_write(&ctx->dif, 0, ctx->app.imem_start, imem_size) !=
      kDifOtbnOk) {
    return kOtbnError;
  }

  if (dmem_size > 0) {
    if (dif_otbn_dmem_write(&ctx->dif, 0, ctx->app.dmem_start, dmem_size) !=
        kDifOtbnOk) {
      return kOtbnError;
    }
  }

  ctx->app_is_loaded = true;
  return kOtbnOk;
}

otbn_result_t otbn_call_function(otbn_t *ctx, otbn_ptr_t func) {
  if (ctx == NULL || !ctx->app_is_loaded) {
    return kOtbnBadArg;
  }

  uint32_t func_imem_addr;
  otbn_result_t result = func_ptr_to_otbn_imem_addr(ctx, func, &func_imem_addr);
  if (result != kOtbnOk) {
    return result;
  }

  if (dif_otbn_start(&ctx->dif, func_imem_addr) != kDifOtbnOk) {
    return kOtbnError;
  }

  return kOtbnOk;
}

otbn_result_t otbn_copy_data_to_otbn(otbn_t *ctx, size_t len_bytes,
                                     const void *src, otbn_ptr_t dest) {
  if (ctx == NULL || dest == NULL) {
    return kOtbnBadArg;
  }

  uint32_t dest_dmem_addr;
  otbn_result_t result = data_ptr_to_otbn_dmem_addr(ctx, dest, &dest_dmem_addr);
  if (result != kOtbnOk) {
    return result;
  }

  if (dif_otbn_dmem_write(&ctx->dif, dest_dmem_addr, src, len_bytes) !=
      kDifOtbnOk) {
    return kOtbnError;
  }
  return kOtbnOk;
}

otbn_result_t otbn_copy_data_from_otbn(otbn_t *ctx, size_t len_bytes,
                                       otbn_ptr_t src, void *dest) {
  if (ctx == NULL || dest == NULL) {
    return kOtbnBadArg;
  }

  uint32_t src_dmem_addr;
  otbn_result_t result = data_ptr_to_otbn_dmem_addr(ctx, src, &src_dmem_addr);
  if (result != kOtbnOk) {
    return result;
  }

  if (dif_otbn_dmem_read(&ctx->dif, src_dmem_addr, dest, len_bytes) !=
      kDifOtbnOk) {
    return kOtbnError;
  }
  return kOtbnOk;
}

otbn_result_t otbn_zero_data_memory(otbn_t *ctx) {
  if (ctx == NULL) {
    return kOtbnBadArg;
  }

  size_t dmem_size_words =
      dif_otbn_get_dmem_size_bytes(&ctx->dif) / sizeof(uint32_t);
  bool retval = kOtbnOk;
  for (size_t i = 0; i < dmem_size_words; ++i) {
    const uint32_t zero = 0;

    // Continue the process even if a single write fails to try to clear as much
    // memory as possible.
    if (dif_otbn_dmem_write(&ctx->dif, i * sizeof(uint32_t), &zero,
                            sizeof(zero)) != kDifOtbnOk) {
      retval = kOtbnError;
    }
  }
  return retval;
}
