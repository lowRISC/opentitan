// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/ip/aes/model/aes_modes.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/otbn.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"  // Generated.

/**
 * Using the AES buffers as reference data to check the memories rather then
 * random data.
 */
#define OTBN_DATA_REF_DMEM_BYTES kAesModesKey256
#define OTBN_DATA_REF_IMEM_BYTES kAesModesPlainText

enum {
  kImemCheckSize = 1024,
  kDmemCheckSize = 1024,
};

static_assert(kImemCheckSize <= OTBN_IMEM_SIZE_BYTES, "Out of bounds");
static_assert(kDmemCheckSize <= OTBN_DMEM_SIZE_BYTES, "Out of bounds");
static_assert(sizeof(kAesModesKey256) % sizeof(uint32_t) == 0,
              "Alignment error");
static_assert(sizeof(kAesModesKey256) % OTBN_IMEM_SIZE_BYTES,
              "Alignment error");

/**
 * `dmemset` is an otbn app to set the whole dmem with a 32 Byte argument.
 */
OTBN_DECLARE_SYMBOL_ADDR(dmemset, set_value);
OTBN_DECLARE_APP_SYMBOLS(dmemset);
static const otbn_app_t kOtbnAppCfiTest = OTBN_APP_T_INIT(dmemset);
static const otbn_addr_t kOtbnSetValue = OTBN_ADDR_T_INIT(dmemset, set_value);

OTTF_DEFINE_TEST_CONFIG();

static volatile bool has_irq_fired;

/**
 * This overrides the default OTTF load/store fault exception handler.
 */
void ottf_load_integrity_error_handler(void) { has_irq_fired = true; }

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
static void otbn_check_mem(otbn_t *ctx, bool match_expected, const uint8_t *ref,
                           size_t ref_len, otbn_read_t otbn_read,
                           size_t mem_size) {
  uint8_t local_buf[ref_len];
  size_t offset = 0;
  do {
    size_t remainder = mem_size - offset;
    if (remainder > ARRAYSIZE(local_buf)) {
      remainder = ARRAYSIZE(local_buf);
    }

    // If the memory has been scrambled we will expect to receive an exception,
    // otherwise we compare the memory value.
    has_irq_fired = false;
    CHECK_DIF_OK(otbn_read(&ctx->dif, offset, local_buf, remainder));
    if (match_expected) {
      CHECK(!has_irq_fired, "Unexpected exception");
      CHECK_ARRAYS_EQ(ref, local_buf, ref_len);
    } else {
      CHECK(has_irq_fired, "Expected exception haven't fired");
      break;
    }
    offset += remainder;
  } while (offset < mem_size);
}

static void otbn_imemset(otbn_t *ctx) {
  for (uint32_t offset = 0; offset < OTBN_IMEM_SIZE_BYTES;
       offset += sizeof(OTBN_DATA_REF_IMEM_BYTES)) {
    CHECK_DIF_OK(dif_otbn_imem_write(&ctx->dif, offset,
                                     OTBN_DATA_REF_IMEM_BYTES,
                                     sizeof(OTBN_DATA_REF_IMEM_BYTES)));
  }
}

static void otbn_dmemset(otbn_t *ctx) {
  CHECK(otbn_load_app(ctx, kOtbnAppCfiTest) == kOtbnOk);
  CHECK(otbn_copy_data_to_otbn(ctx, sizeof(OTBN_DATA_REF_DMEM_BYTES),
                               OTBN_DATA_REF_DMEM_BYTES,
                               kOtbnSetValue) == kOtbnOk);
  CHECK(otbn_execute(ctx) == kOtbnOk);
  CHECK(otbn_busy_wait_for_done(ctx) == kOtbnOk);
}

static void otbn_wipe_memories(otbn_t *ctx) {
  CHECK_DIF_OK(dif_otbn_write_cmd(&ctx->dif, kDifOtbnCmdSecWipeImem));
  CHECK(otbn_busy_wait_for_done(ctx) == kOtbnOk);
  CHECK_DIF_OK(dif_otbn_write_cmd(&ctx->dif, kDifOtbnCmdSecWipeDmem));
  CHECK(otbn_busy_wait_for_done(ctx) == kOtbnOk);
}

bool test_main(void) {
  otbn_t otbn_ctx;
  mmio_region_t addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR);
  CHECK(otbn_init(&otbn_ctx, addr) == kOtbnOk);

  // Initialize the entropy_src subsystem to enable OTP_CTRL fetch random data
  // (already done by the test_rom startup code).
  entropy_testutils_boot_mode_init();

  // Have OTBN fetch a new key and nonce from the OTP_CTRL by issuing a DMEM and
  // IMEM wipe command.
  otbn_wipe_memories(&otbn_ctx);

  // Write and read-check OTBN and IMEM for consistency.
  otbn_dmemset(&otbn_ctx);
  otbn_check_mem(&otbn_ctx,
                 /*match_expected=*/true, OTBN_DATA_REF_DMEM_BYTES,
                 sizeof(OTBN_DATA_REF_DMEM_BYTES), dif_otbn_dmem_read,
                 kDmemCheckSize);
  otbn_imemset(&otbn_ctx);
  otbn_check_mem(&otbn_ctx,
                 /*match_expected=*/true, OTBN_DATA_REF_IMEM_BYTES,
                 sizeof(OTBN_DATA_REF_IMEM_BYTES), dif_otbn_imem_read,
                 kImemCheckSize);

  // Fetch a new key from the OTP_CTRL by issuing a DMEM and IMEM wipe command.
  otbn_wipe_memories(&otbn_ctx);

  // Verify that IMEM and DMEM can not be read by waiting for a internal
  // interruption.
  otbn_check_mem(&otbn_ctx,
                 /*match_expected=*/false, OTBN_DATA_REF_DMEM_BYTES,
                 sizeof(uint32_t), dif_otbn_imem_read, sizeof(uint32_t));
  otbn_check_mem(&otbn_ctx,
                 /*match_expected=*/false, OTBN_DATA_REF_DMEM_BYTES,
                 sizeof(uint32_t), dif_otbn_dmem_read, sizeof(uint32_t));
  return true;
}
