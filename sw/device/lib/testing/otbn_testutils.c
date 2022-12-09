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

void otbn_testutils_wait_for_done(const dif_otbn_t *otbn,
                                  dif_otbn_err_bits_t expected_err_bits) {
  bool busy = true;
  dif_otbn_status_t status;
  while (busy) {
    CHECK_DIF_OK(dif_otbn_get_status(otbn, &status));
    busy = status != kDifOtbnStatusIdle && status != kDifOtbnStatusLocked;
  }

  // Error out if OTBN is locked.
  CHECK(status == kDifOtbnStatusIdle, "OTBN is locked.");

  dif_otbn_err_bits_t err_bits;
  CHECK_DIF_OK(dif_otbn_get_err_bits(otbn, &err_bits));
  CHECK(err_bits == expected_err_bits, "OTBN error bits: got: 0x%x, want: 0x%x",
        err_bits, expected_err_bits);
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

void otbn_testutils_load_app(const dif_otbn_t *otbn, const otbn_app_t app) {
  check_app_address_ranges(&app);

  const size_t imem_size = app.imem_end - app.imem_start;
  const size_t data_size = app.dmem_data_end - app.dmem_data_start;

  // Memory images and offsets must be multiples of 32b words.
  CHECK(imem_size % sizeof(uint32_t) == 0);
  CHECK(data_size % sizeof(uint32_t) == 0);

  CHECK_DIF_OK(dif_otbn_imem_write(otbn, 0, app.imem_start, imem_size));

  // Write initialized data
  if (data_size > 0) {
    CHECK_DIF_OK(dif_otbn_dmem_write(otbn, 0, app.dmem_data_start, data_size));
  }
}

void otbn_testutils_execute(const dif_otbn_t *otbn) {
  CHECK_DIF_OK(dif_otbn_write_cmd(otbn, kDifOtbnCmdExecute));
}

void otbn_testutils_write_data(const dif_otbn_t *otbn, size_t len_bytes,
                               const void *src, otbn_addr_t dest) {
  CHECK_DIF_OK(dif_otbn_dmem_write(otbn, dest, src, len_bytes));
}

void otbn_testutils_read_data(const dif_otbn_t *otbn, size_t len_bytes,
                              otbn_addr_t src, void *dest) {
  CHECK_DIF_OK(dif_otbn_dmem_read(otbn, src, dest, len_bytes));
}

void otbn_dump_dmem(const dif_otbn_t *otbn, uint32_t max_addr) {
  CHECK(max_addr % kOtbnWlenBytes == 0);

  if (max_addr == 0) {
    max_addr = dif_otbn_get_dmem_size_bytes(otbn);
  }

  for (int i = 0; i < max_addr; i += kOtbnWlenBytes) {
    uint32_t data[kOtbnWlenBytes / sizeof(uint32_t)];
    CHECK_DIF_OK(dif_otbn_dmem_read(otbn, i, data, kOtbnWlenBytes));
    LOG_INFO("DMEM @%04d: 0x%08x%08x%08x%08x%08x%08x%08x%08x",
             i / kOtbnWlenBytes, data[7], data[6], data[5], data[4], data[3],
             data[2], data[1], data[0]);
  }
}
