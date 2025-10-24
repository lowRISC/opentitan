// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top/dt/dt_csrng.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/csrng_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

static_assert(kDtCsrngCount >= 1,
              "This test requires at least one CSRNG instance");

static const dt_csrng_t kTestCsrng = (dt_csrng_t)0;

OTTF_DEFINE_TEST_CONFIG();

enum {
  kExpectedOutputLen = 16,
};

/**
 * Run CTR DRBG Known-Answer-Tests (KATs).
 *
 * This is a simplified version of csrng_kat_test. It skips CSRNG internal
 * state checks to optimize runtime.
 */
status_t test_ctr_drbg_ctr0_smoke(const dif_csrng_t *csrng) {
  CHECK_DIF_OK(dif_csrng_uninstantiate(csrng));

  const dif_csrng_seed_material_t kEntropyInput = {
      .seed_material = {0x73bec010, 0x9262474c, 0x16a30f76, 0x531b51de,
                        0x2ee494e5, 0xdfec9db3, 0xcb7a879d, 0x5600419c,
                        0xca79b0b0, 0xdda33b5c, 0xa468649e, 0xdf5d73fa},
      .seed_material_len = 12,
  };
  TRY(csrng_testutils_cmd_ready_wait(csrng));
  CHECK_DIF_OK(dif_csrng_instantiate(csrng, kDifCsrngEntropySrcToggleDisable,
                                     &kEntropyInput));

  uint32_t got[kExpectedOutputLen];
  TRY(csrng_testutils_cmd_generate_run(csrng, NULL, got, kExpectedOutputLen));
  TRY(csrng_testutils_cmd_generate_run(csrng, NULL, got, kExpectedOutputLen));

  const uint32_t kExpectedOutput[kExpectedOutputLen] = {
      0xe48bb8cb, 0x1012c84c, 0x5af8a7f1, 0xd1c07cd9, 0xdf82ab22, 0x771c619b,
      0xd40fccb1, 0x87189e99, 0x510494b3, 0x64f7ac0c, 0x2581f391, 0x80b1dc2f,
      0x793e01c5, 0x87b107ae, 0xdb17514c, 0xa43c41b7,
  };
  CHECK_ARRAYS_EQ(got, kExpectedOutput, kExpectedOutputLen,
                  "Generate command KAT output mismatch");
  return OK_STATUS();
}

bool test_main(void) {
  dif_csrng_t csrng;
  CHECK_DIF_OK(dif_csrng_init_from_dt(kTestCsrng, &csrng));
  CHECK_DIF_OK(dif_csrng_configure(&csrng));
  CHECK_STATUS_OK(test_ctr_drbg_ctr0_smoke(&csrng));
  return true;
}
