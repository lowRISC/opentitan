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

uint32_t otbn_data_ptr_to_dmem_addr(const otbn_t *ctx, otbn_ptr_t ptr) {
  return (uintptr_t)ptr - (uintptr_t)ctx->app.dmem_start;
}

otbn_ptr_t otbn_dmem_addr_to_data_ptr(const otbn_t *ctx, uint32_t dmem_addr) {
  return (otbn_ptr_t)((uintptr_t)ctx->app.dmem_start + (uintptr_t)dmem_addr);
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

otbn_error_t otbn_load_app(otbn_t *ctx, const otbn_app_t app) {
  if (app.imem_end <= app.imem_start || app.dmem_end < app.dmem_start) {
    return kOtbnErrorInvalidArgument;
  }

  const size_t imem_num_words = app.imem_end - app.imem_start;
  const size_t dmem_num_words = app.dmem_end - app.dmem_start;

  ctx->app_is_loaded = false;

  OTBN_RETURN_IF_ERROR(otbn_imem_write(0, app.imem_start, imem_num_words));

  otbn_zero_dmem();
  if (dmem_num_words > 0) {
    OTBN_RETURN_IF_ERROR(otbn_dmem_write(0, app.dmem_start, dmem_num_words));
  }

  ctx->app = app;
  ctx->app_is_loaded = true;
  ctx->free_dmem = (otbn_ptr_t)app.dmem_end;
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
  uint32_t dest_dmem_addr = otbn_data_ptr_to_dmem_addr(ctx, dest);
  OTBN_RETURN_IF_ERROR(otbn_dmem_write(dest_dmem_addr, src, len));

  return kOtbnErrorOk;
}

otbn_error_t otbn_copy_data_from_otbn(otbn_t *ctx, size_t len, otbn_ptr_t src,
                                      uint32_t *dest) {
  uint32_t src_dmem_addr = otbn_data_ptr_to_dmem_addr(ctx, src);
  OTBN_RETURN_IF_ERROR(otbn_dmem_read(src_dmem_addr, dest, len));

  return kOtbnErrorOk;
}

/**
 * Rounds a pointer up to the next 256-bit-aligned DMEM address.
 *
 * The alignment is with respect to DMEM's address space, not the CPU's.
 *
 * @param otbn The OTBN context object.
 * @param ptr The OTBN pointer to align.
 * @return The new, aligned pointer
 */
static otbn_ptr_t otbn_pointer_balign_wide(otbn_t *otbn, otbn_ptr_t ptr) {
  // Extract the DMEM relative address.
  uint32_t addr = otbn_data_ptr_to_dmem_addr(otbn, ptr);
  uint32_t misalign = addr & 31;
  if (misalign == 0) {
    // Already 32-byte aligned; done
    return ptr;
  }
  // Get the next 32-byte aligned address
  addr += (32 - misalign);
  return otbn_dmem_addr_to_data_ptr(otbn, addr);
}

/**
 * Increments an OTBN pointer by `len`.
 *
 * Afterwards, the pointer points to a DMEM region `len` bytes after the
 * original pointer pointed to. For instance, if you wrote 5 bytes to the
 * location at the original pointer, incrementing the pointer by 5 would make
 * the pointer point to the end of the region you just wrote.
 *
 * @param otbn The OTBN context
 * @param ptr The OTBN pointer to align.
 * @param len Number of DMEM bytes to advance the pointer.
 * @return The new, incremented pointer
 */
static otbn_ptr_t otbn_pointer_inc(otbn_t *otbn, otbn_ptr_t ptr, uint32_t len) {
  // Extract the DMEM relative address.
  uint32_t addr = otbn_data_ptr_to_dmem_addr(otbn, ptr);
  addr += len;
  return otbn_dmem_addr_to_data_ptr(otbn, addr);
}

otbn_error_t set_data_pointer(otbn_t *otbn, const otbn_ptr_t dptr,
                              const otbn_ptr_t value) {
  uint32_t value_dmem_addr = otbn_data_ptr_to_dmem_addr(otbn, value);
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(otbn, 1, &value_dmem_addr, dptr));
  return kOtbnErrorOk;
}

otbn_error_t otbn_dmem_alloc(otbn_t *otbn, size_t len, otbn_ptr_t dptr) {
  if (!otbn->app_is_loaded) {
    return kOtbnErrorInvalidArgument;
  }
  // Set dest to the next aligned, free address.
  otbn_ptr_t dest = otbn_pointer_balign_wide(otbn, otbn->free_dmem);
  // Set up the dptr to point to dest.
  OTBN_RETURN_IF_ERROR(set_data_pointer(otbn, dptr, dest));
  // Increment the pointer by the number of bytes allocated.
  otbn->free_dmem = otbn_pointer_inc(otbn, dest, len * sizeof(uint32_t));
  // Check that there was enough space in DMEM for this allocation (including
  // checking whether the pointer increment overflowed).
  uint32_t free_dmem_addr = otbn_data_ptr_to_dmem_addr(otbn, otbn->free_dmem);
  if (free_dmem_addr >= kOtbnDMemSizeBytes ||
      free_dmem_addr < len * sizeof(uint32_t)) {
    return kOtbnErrorBadOffsetLen;
  }
  return kOtbnErrorOk;
}

otbn_error_t otbn_dmem_write_indirect(otbn_t *otbn, size_t len,
                                      const uint32_t *src, otbn_ptr_t dptr) {
  if (!otbn->app_is_loaded) {
    return kOtbnErrorInvalidArgument;
  }
  // Set dest to the next aligned, free address and write data.
  otbn_ptr_t dest = otbn_pointer_balign_wide(otbn, otbn->free_dmem);
  OTBN_RETURN_IF_ERROR(otbn_copy_data_to_otbn(otbn, len, src, dest));
  // Set up the dptr to point to dest.
  OTBN_RETURN_IF_ERROR(set_data_pointer(otbn, dptr, dest));
  // Increment the pointer by the number of bytes written.
  otbn->free_dmem = otbn_pointer_inc(otbn, dest, len * sizeof(uint32_t));
  return kOtbnErrorOk;
}

otbn_error_t otbn_dmem_read_indirect(otbn_t *otbn, size_t len, otbn_ptr_t dptr,
                                     uint32_t *dest) {
  // Read one word from DMEM[dptr]
  uint32_t src_addr;
  OTBN_RETURN_IF_ERROR(otbn_copy_data_from_otbn(otbn, 1, dptr, &src_addr));
  // Convert the DMEM address to an OTBN pointer
  otbn_ptr_t src = otbn_dmem_addr_to_data_ptr(otbn, src_addr);
  // Copy data from DMEM
  OTBN_RETURN_IF_ERROR(otbn_copy_data_from_otbn(otbn, len, src, dest));
  return kOtbnErrorOk;
}
