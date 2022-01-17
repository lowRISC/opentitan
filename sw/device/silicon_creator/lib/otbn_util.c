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

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

void otbn_init(otbn_t *ctx) {
  *ctx = (otbn_t){
      .app = {0},
      .app_is_loaded = false,
      .error_bits = kOtbnErrBitsNoError,
  };
}

otbn_error_t otbn_data_ptr_to_dmem_addr(const otbn_t *ctx, otbn_ptr_t ptr,
                                        uint32_t *dmem_addr_otbn) {
  uintptr_t ptr_addr = (uintptr_t)ptr;
  uintptr_t app_dmem_data_start_addr = (uintptr_t)ctx->app.dmem_data_start;
  uintptr_t app_dmem_data_end_addr = (uintptr_t)ctx->app.dmem_data_end;
  uintptr_t app_dmem_bss_start_addr = (uintptr_t)ctx->app.dmem_bss_start;
  uintptr_t app_dmem_bss_end_addr = (uintptr_t)ctx->app.dmem_bss_end;
  uintptr_t app_dmem_bss_offset = (uintptr_t)ctx->app.dmem_bss_offset;

  if (app_dmem_data_start_addr <= ptr_addr &&
      ptr_addr < app_dmem_data_end_addr) {
    // Pointer is in the `data` section, which is at the start of DMEM
    *dmem_addr_otbn = ptr_addr - app_dmem_data_start_addr;
  } else if (app_dmem_bss_start_addr <= ptr_addr &&
             ptr_addr < app_dmem_bss_end_addr) {
    // Pointer is in the `bss` section, which is after the data section in DMEM
    *dmem_addr_otbn = ptr_addr - app_dmem_bss_start_addr + app_dmem_bss_offset;
  } else {
    // Pointer is not in a valid DMEM region
    return kOtbnErrorInvalidArgument;
  }
  return kOtbnErrorOk;
}

otbn_error_t otbn_busy_wait_for_done(otbn_t *ctx) {
  while (otbn_is_busy()) {
  }

  otbn_err_bits_t err_bits;
  otbn_get_err_bits(&err_bits);
  if (err_bits != kOtbnErrBitsNoError) {
    ctx->error_bits = err_bits;
    return kOtbnErrorExecutionFailed;
  }
  return kOtbnErrorOk;
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
  // Both DMEM sections must not be backwards
  if (app->dmem_data_end < app->dmem_data_start ||
      app->dmem_bss_end < app->dmem_bss_start) {
    return false;
  }
  // The offset of BSS in DMEM address space must be at least as large as the
  // data section (i.e. the sections do not overlap in DMEM)
  if (app->dmem_bss_offset <
      (uintptr_t)app->dmem_data_end - (uintptr_t)app->dmem_data_start) {
    return false;
  }
  return true;
}

otbn_error_t otbn_load_app(otbn_t *ctx, const otbn_app_t app) {
  if (!check_app_address_ranges(&app)) {
    return kOtbnErrorInvalidArgument;
  }

  const size_t imem_num_words = app.imem_end - app.imem_start;
  const size_t data_num_words = app.dmem_data_end - app.dmem_data_start;

  ctx->app_is_loaded = false;

  OTBN_RETURN_IF_ERROR(otbn_imem_write(0, app.imem_start, imem_num_words));

  otbn_zero_dmem();
  if (data_num_words > 0) {
    OTBN_RETURN_IF_ERROR(
        otbn_dmem_write(0, app.dmem_data_start, data_num_words));
  }

  ctx->app = app;
  ctx->app_is_loaded = true;
  return kOtbnErrorOk;
}

otbn_error_t otbn_execute_app(otbn_t *ctx) {
  if (!ctx->app_is_loaded) {
    return kOtbnErrorInvalidArgument;
  }

  otbn_execute();
  return kOtbnErrorOk;
}

otbn_error_t otbn_copy_data_to_otbn(otbn_t *ctx, size_t len,
                                    const uint32_t *src, otbn_ptr_t dest) {
  uint32_t dest_dmem_addr;
  OTBN_RETURN_IF_ERROR(otbn_data_ptr_to_dmem_addr(ctx, dest, &dest_dmem_addr));
  OTBN_RETURN_IF_ERROR(otbn_dmem_write(dest_dmem_addr, src, len));

  return kOtbnErrorOk;
}

otbn_error_t otbn_copy_data_from_otbn(otbn_t *ctx, size_t len_bytes,
                                      otbn_ptr_t src, uint32_t *dest) {
  uint32_t src_dmem_addr;
  OTBN_RETURN_IF_ERROR(otbn_data_ptr_to_dmem_addr(ctx, src, &src_dmem_addr));
  OTBN_RETURN_IF_ERROR(otbn_dmem_read(src_dmem_addr, dest, len_bytes));

  return kOtbnErrorOk;
}
