// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/hmac_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

#define RUN_TEST(test_)                    \
  LOG_INFO("Starting test " #test_ "..."); \
  test_();                                 \
  LOG_INFO("Finished test " #test_ ": ok.");

#define CHECK_WORD_ALIGNED(addr_)                 \
  CHECK((uintptr_t)addr_ % sizeof(uint32_t) == 0, \
        #addr_ " must be word aligned");

void boot_measurements_test(void) {
  CHECK(kManifest.usage_constraints.selector_bits == 0,
        "Selector bits must be 0");
  const volatile char *manifest_start = (const volatile char *)&kManifest;
  const char *manifest_end = (const char *)manifest_start + sizeof(manifest_t);
  const volatile char *signed_region_start =
      manifest_start + sizeof(sigverify_rsa_buffer_t);
  const char *signed_region_end =
      (const char *)manifest_start + kManifest.length;
  size_t manifest_signed_region_size = manifest_end - signed_region_start;
  size_t signed_region_size = signed_region_end - signed_region_start;
  dif_hmac_t hmac;

  CHECK_WORD_ALIGNED(manifest_start);
  CHECK_WORD_ALIGNED(manifest_end);
  CHECK_WORD_ALIGNED(signed_region_start);
  CHECK_WORD_ALIGNED(signed_region_end);
  CHECK_WORD_ALIGNED(manifest_signed_region_size);
  CHECK_WORD_ALIGNED(signed_region_size);

  CHECK_DIF_OK(
      dif_hmac_init(mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR), &hmac));
  CHECK_DIF_OK(dif_hmac_mode_sha256_start(
      &hmac, (dif_hmac_transaction_t){
                 .digest_endianness = kDifHmacEndiannessLittle,
                 .message_endianness = kDifHmacEndiannessLittle,
             }));

  // Copy the part of the manifest that's in the signed region to
  // memory before pushing to hmac since it's volatile.
  // Note: this array is larger than `manifest_signed_region_size` since VLAs
  // are optional in C11.
  char manifest_signed_region[sizeof(manifest_t)];
  for (size_t i = 0; i < manifest_signed_region_size; ++i) {
    manifest_signed_region[i] =
        *((const volatile char *)signed_region_start + i);
  }
  hmac_testutils_push_message(&hmac, manifest_signed_region,
                              manifest_signed_region_size);
  // Rest of the image
  hmac_testutils_push_message(&hmac, manifest_end,
                              signed_region_size - manifest_signed_region_size);

  CHECK_DIF_OK(dif_hmac_process(&hmac));
  dif_hmac_digest_t act_digest;
  hmac_testutils_finish_polled(&hmac, &act_digest);

  CHECK_ARRAYS_EQ(boot_measurements.rom_ext.data, act_digest.digest,
                  ARRAYSIZE(act_digest.digest));
}

void sec_mmio_pos_test(void) {
  enum {
    kRndOffset = 13,
    kRomCheckValue = 6,
  };

  sec_mmio_check_values(kRndOffset);
  sec_mmio_check_counters(kRomCheckValue + 1);
}

static volatile bool exception_expected = false;
static volatile bool exception_observed = false;

// Redeclaration of the addressable symbol in `sec_mmio_neg_test()` to be used
// in `ottf_exception_handler()`.
extern const char kSecMmioNegTestReturn[];

void ottf_exception_handler(void) {
  CHECK(exception_expected == true);
  CHECK(exception_observed == false);
  exception_expected = false;
  // The frame address is the address of the stack location that holds the
  // `mepc`, since the OTTF exception handler entry code saves the `mepc` to
  // the top of the stack before transferring control flow to the exception
  // handler function (which is overridden here). See the `handler_exception`
  // subroutine in `sw/device/lib/testing/testing/ottf_isrs.S` for more details.
  uintptr_t *mepc_stack_addr = (uintptr_t *)OT_FRAME_ADDR();
  ibex_exc_t exception = ibex_mcause_read();
  switch (exception) {
    case kIbexExcIllegalInstrFault:
      LOG_INFO("Observed illegal instruction fault");
      exception_observed = true;
      *mepc_stack_addr = (uintptr_t)kSecMmioNegTestReturn;
      break;
    default:
      LOG_FATAL("Unexpected exception id = 0x%x", exception);
      abort();
  }
}

void sec_mmio_neg_test(void) {
  exception_expected = true;
  sec_mmio_check_counters(0);
  CHECK(false, "Should not be here");

  OT_ADDRESSABLE_LABEL(kSecMmioNegTestReturn);
  CHECK(exception_observed == true);
}

bool test_main(void) {
  RUN_TEST(boot_measurements_test);
  RUN_TEST(sec_mmio_pos_test);
  RUN_TEST(sec_mmio_neg_test);
  return true;
}
