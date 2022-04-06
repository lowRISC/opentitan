// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/otbn.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTBN_DECLARE_APP_SYMBOLS(randomness);
static const otbn_app_t kOtbnAppCfiTest = OTBN_APP_T_INIT(randomness);

const test_config_t kTestConfig;

static volatile bool has_exception_fired;

/**
 * This overrides the default OTTF load/store fault exception handler.
 */
void ottf_load_store_fault_handler(void) { has_exception_fired = true; }

typedef dif_result_t (*otbn_read_t)(const dif_otbn_t *otbn,
                                    uint32_t offset_bytes, void *dest,
                                    size_t len_bytes);
/**
 * Check whether the contents of an otbn memory match the reference data pointed
 * at `addr`.
 *
 * @param ctx The otbn context object.
 * @param addr The address of the reference data.
 * @param mem_size The size of the reference data.
 * @param match_expected Indicates whether the checking is expected to match.
 * @param read_function Pointer to the function to read the data. It can be
 * either `dif_otbn_imem_read` or `dif_otbn_dmem_read`.
 */
static void otbn_check_mem(otbn_t *ctx, const uint8_t *addr, size_t mem_size,
                           bool match_expected, otbn_read_t otbn_read) {
  uint8_t local_buf[256];
  size_t offset = 0;
  do {
    size_t remainder = mem_size - offset;
    if (remainder > ARRAYSIZE(local_buf)) {
      remainder = ARRAYSIZE(local_buf);
    }

    // If the memory has been scrambled we will expect to receive an exception,
    // otherwise we compare the memory value.
    has_exception_fired = false;
    CHECK_DIF_OK(otbn_read(&ctx->dif, offset, local_buf, remainder));
    if (match_expected) {
      CHECK(!has_exception_fired, "Unexpected exception");
      CHECK_BUFFER_EQ(addr + offset, local_buf, remainder);
    } else {
      CHECK(has_exception_fired, "Expected exception haven't fired");
      break;
    }

    offset += remainder;
  } while (offset < mem_size);
}

/**
 * Check that the application is loaded correctly to the IMEM and DMEM.
 *
 * @param ctx The otbn context object.
 * @param app The application to match with OTBN memory.
 * @param match_expected Indicates whether the checking is expected to match.
 */
static void otbn_check_app(otbn_t *ctx, const otbn_app_t app,
                           bool match_expected) {
  const size_t imem_size = app.imem_end - app.imem_start;
  const size_t data_size = app.dmem_data_end - app.dmem_data_start;
  const uint8_t *imem_start = app.imem_start;
  const uint8_t *dmem_start = app.dmem_data_start;

  // Memory images and offsets must be multiples of 32b words.
  CHECK(imem_size % sizeof(uint32_t) == 0);

  // Check the IMEM content.
  otbn_check_mem(ctx, imem_start, imem_size, match_expected,
                 dif_otbn_imem_read);

  // Check the DMEM content.
  otbn_check_mem(ctx, dmem_start, data_size, match_expected,
                 dif_otbn_dmem_read);
}

bool test_main() {
  otbn_t otbn_ctx;
  mmio_region_t addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR);
  CHECK(otbn_init(&otbn_ctx, addr) == kOtbnOk);

  // Write and read-check OTBN and IMEM for consistency.
  CHECK(otbn_load_app(&otbn_ctx, kOtbnAppCfiTest) == kOtbnOk);
  otbn_check_app(&otbn_ctx, kOtbnAppCfiTest, /*match_expected=*/true);

  // Fetch a new key from the OTP_CTRL and ensure that previous contents in the
  // IMEM and DMEM cannot be read anymore.
  CHECK_DIF_OK(dif_otbn_write_cmd(&otbn_ctx.dif, kDifOtbnCmdSecWipeImem));
  CHECK(otbn_busy_wait_for_done(&otbn_ctx) == kOtbnOk);
  CHECK_DIF_OK(dif_otbn_write_cmd(&otbn_ctx.dif, kDifOtbnCmdSecWipeDmem));
  CHECK(otbn_busy_wait_for_done(&otbn_ctx) == kOtbnOk);
  otbn_check_app(&otbn_ctx, kOtbnAppCfiTest, /*match_expected=*/false);

  return true;
}
