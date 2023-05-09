// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/otbn_testutils.h"

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"

enum {
  /**
   * Data width of big number subset, in bytes.
   */
  kOtbnWlenBytes = 256 / 8,
};

status_t otbn_testutils_wait_for_done(const dif_otbn_t *otbn,
                                      dif_otbn_err_bits_t expected_err_bits) {
  bool busy = true;
  dif_otbn_status_t status;
  while (busy) {
    TRY(dif_otbn_get_status(otbn, &status));
    busy = status != kDifOtbnStatusIdle && status != kDifOtbnStatusLocked;
  }

  // Get instruction count so that we can print them to help with debugging.
  uint32_t instruction_count;
  TRY(dif_otbn_get_insn_cnt(otbn, &instruction_count));

  dif_otbn_err_bits_t err_bits;
  TRY(dif_otbn_get_err_bits(otbn, &err_bits));

  // Error out if OTBN is locked.
  TRY_CHECK(status == kDifOtbnStatusIdle, "OTBN is locked. Error bits: 0x%08x",
            err_bits);

  // Error out if error bits do not match expectations.
  TRY_CHECK(
      err_bits == expected_err_bits,
      "OTBN error bits: got: 0x%08x, expected: 0x%08x.\nInstruction count: "
      "0x%08x",
      err_bits, expected_err_bits, instruction_count);
  return OK_STATUS();
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
 */
static void check_app_address_ranges(const otbn_app_t *app) {
  // IMEM must have a strictly positive range (cannot be backwards or empty)
  CHECK(app->imem_end > app->imem_start);
  // Initialised DMEM section must not be backwards
  CHECK(app->dmem_data_end >= app->dmem_data_start);
}

status_t otbn_testutils_load_app(const dif_otbn_t *otbn, const otbn_app_t app) {
  check_app_address_ranges(&app);

  const size_t imem_size = (size_t)(app.imem_end - app.imem_start);
  const size_t data_size = (size_t)(app.dmem_data_end - app.dmem_data_start);

  // Memory images and offsets must be multiples of 32b words.
  TRY_CHECK(imem_size % sizeof(uint32_t) == 0);
  TRY_CHECK(data_size % sizeof(uint32_t) == 0);

  TRY(dif_otbn_imem_write(otbn, 0, app.imem_start, imem_size));

  // Write initialized data
  if (data_size > 0) {
    TRY(dif_otbn_dmem_write(otbn, 0, app.dmem_data_start, data_size));
  }
  return OK_STATUS();
}

status_t otbn_testutils_execute(const dif_otbn_t *otbn) {
  TRY(dif_otbn_write_cmd(otbn, kDifOtbnCmdExecute));
  return OK_STATUS();
}

status_t otbn_testutils_write_data(const dif_otbn_t *otbn, size_t len_bytes,
                                   const void *src, otbn_addr_t dest) {
  TRY(dif_otbn_dmem_write(otbn, dest, src, len_bytes));
  return OK_STATUS();
}

status_t otbn_testutils_read_data(const dif_otbn_t *otbn, size_t len_bytes,
                                  otbn_addr_t src, void *dest) {
  TRY(dif_otbn_dmem_read(otbn, src, dest, len_bytes));
  return OK_STATUS();
}

status_t otbn_dump_dmem(const dif_otbn_t *otbn, uint32_t max_addr) {
  TRY_CHECK(max_addr % kOtbnWlenBytes == 0);

  if (max_addr == 0) {
    max_addr = dif_otbn_get_dmem_size_bytes(otbn);
  }

  TRY_CHECK(max_addr <= UINT32_MAX, "max_addr must fit in uint32_t");
  for (uint32_t i = 0; i < max_addr; i += kOtbnWlenBytes) {
    uint32_t data[kOtbnWlenBytes / sizeof(uint32_t)];
    TRY(dif_otbn_dmem_read(otbn, i, data, kOtbnWlenBytes));
    LOG_INFO("DMEM @%04d: 0x%08x%08x%08x%08x%08x%08x%08x%08x",
             i / kOtbnWlenBytes, data[7], data[6], data[5], data[4], data[3],
             data[2], data[1], data[0]);
  }
  return OK_STATUS();
}
