// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/csrng_testutils.h"

#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "csrng_regs.h"  // Generated

enum {
  kNumOutputWordsMax = 16,
};

void csrng_testutils_cmd_ready_wait(const dif_csrng_t *csrng) {
  dif_csrng_cmd_status_t cmd_status;
  do {
    CHECK_DIF_OK(dif_csrng_get_cmd_interface_status(csrng, &cmd_status));
    CHECK(cmd_status.kind != kDifCsrngCmdStatusError);
  } while (cmd_status.kind != kDifCsrngCmdStatusReady);
}

void csrng_testutils_cmd_generate_run(const dif_csrng_t *csrng,
                                      uint32_t *output, size_t output_len) {
  csrng_testutils_cmd_ready_wait(csrng);
  CHECK_DIF_OK(dif_csrng_generate_start(csrng, output_len));

  dif_csrng_output_status_t output_status;
  do {
    CHECK_DIF_OK(dif_csrng_get_output_status(csrng, &output_status));
  } while (!output_status.valid_data);

  CHECK_DIF_OK(dif_csrng_generate_read(csrng, output, output_len));
}

void csrng_testutils_check_internal_state(
    const dif_csrng_t *csrng, const dif_csrng_internal_state_t *expected) {
  csrng_testutils_cmd_ready_wait(csrng);
  dif_csrng_internal_state_t got;
  CHECK_DIF_OK(
      dif_csrng_get_internal_state(csrng, kCsrngInternalStateIdSw, &got));

  CHECK(got.instantiated == expected->instantiated);
  CHECK(got.reseed_counter == expected->reseed_counter);
  CHECK(got.fips_compliance == expected->fips_compliance);

  CHECK_ARRAYS_EQ(got.v, expected->v, ARRAYSIZE(expected->v),
                  "CSRNG internal V buffer mismatch.");

  CHECK_ARRAYS_EQ(got.key, expected->key, ARRAYSIZE(expected->key),
                  "CSRNG internal K buffer mismatch.");
}

void csrng_testutils_kat_instantiate(
    const dif_csrng_t *csrng, bool fail_expected,
    const dif_csrng_seed_material_t *seed_material,
    const dif_csrng_internal_state_t *expected_state) {
  LOG_INFO("CSRNG KAT instantiate");
  CHECK_DIF_OK(dif_csrng_uninstantiate(csrng));

  // Instantiate CSRNG - use the provided seed material only.
  csrng_testutils_cmd_ready_wait(csrng);
  CHECK_DIF_OK(dif_csrng_instantiate(csrng, kDifCsrngEntropySrcToggleDisable,
                                     seed_material));

  // Check the internal state of created CSRNG instance.
  const dif_csrng_internal_state_t kZeroState = {};
  csrng_testutils_check_internal_state(
      csrng, fail_expected ? &kZeroState : expected_state);
}

void csrng_testutils_kat_generate(
    const dif_csrng_t *csrng, size_t num_generates, size_t output_len,
    const uint32_t *expected_output,
    const dif_csrng_internal_state_t *expected_state) {
  LOG_INFO("CSRNG KAT generate");

  // Run the generate and check the output.
  uint32_t got[kNumOutputWordsMax];
  for (int i = 0; i < num_generates; ++i) {
    csrng_testutils_cmd_generate_run(csrng, got, output_len);
  }
  CHECK_ARRAYS_EQ(got, expected_output, output_len,
                  "Generate command KAT output mismatch");

  // Check the internal state.
  csrng_testutils_check_internal_state(csrng, expected_state);
}

void csrng_testutils_kat_reseed(
    const dif_csrng_t *csrng, const dif_csrng_seed_material_t *seed_material,
    const dif_csrng_internal_state_t *expected_state) {
  LOG_INFO("CSRNG KAT reseed");

  // Reseed CSRNG - use the provided seed material only.
  csrng_testutils_cmd_ready_wait(csrng);
  CHECK_DIF_OK(csrng_send_app_cmd(
      csrng->base_addr, CSRNG_CMD_REQ_REG_OFFSET,
      (csrng_app_cmd_t){
          .id = kCsrngAppCmdReseed,
          .entropy_src_enable = kDifCsrngEntropySrcToggleDisable,
          .seed_material = seed_material,
      }));

  // Check the internal state.
  csrng_testutils_check_internal_state(csrng, expected_state);
}

void csrng_testutils_fips_instantiate_kat(const dif_csrng_t *csrng,
                                          bool fail_expected) {
  // CTR_DRBG Known-Answer-Tests (KATs).
  //
  // Test vector sourced from NIST's CAVP website:
  // https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/random-number-generators
  //
  // The number format in this docstring follows the CAVP format to simplify
  // auditing of this test case.
  //
  // Test vector: CTR_DRBG AES-256 no DF.
  //
  // - EntropyInput =
  // df5d73faa468649edda33b5cca79b0b05600419ccb7a879ddfec9db32ee494e5531b51de16a30f769262474c73bec010
  // - Nonce = EMPTY
  // - PersonalizationString = EMPTY
  //
  // Command: Instantiate
  // - Key = 8c52f901632d522774c08fad0eb2c33b98a701a1861aecf3d8a25860941709fd
  // - V   = 217b52142105250243c0b2c206b8f59e
  //
  // Command: Generate (first call):
  // - Key = 72f4af5c93258eb3eeec8c0cacea6c1d1978a4fad44312725f1ac43b167f2d52
  // - V   = e86f6d07dfb551cebad80e6bf6830ac4
  //
  // Command: Generate (second call):
  // - Key = 1a1c6e5f1cccc6974436e5fd3f015bc8e9dc0f90053b73e3c19d4dfd66d1b85a
  // - V   = 53c78ac61a0bac9d7d2e92b1e73e3392
  // - ReturnedBits =
  // d1c07cd95af8a7f11012c84ce48bb8cb87189e99d40fccb1771c619bdf82ab2280b1dc2f2581f39164f7ac0c510494b3a43c41b7db17514c87b107ae793e01c5

  const dif_csrng_seed_material_t kEntropyInput = {
      .seed_material = {0x73bec010, 0x9262474c, 0x16a30f76, 0x531b51de,
                        0x2ee494e5, 0xdfec9db3, 0xcb7a879d, 0x5600419c,
                        0xca79b0b0, 0xdda33b5c, 0xa468649e, 0xdf5d73fa},
      .seed_material_len = 12,
  };
  const dif_csrng_internal_state_t kExpectedState = {
      .reseed_counter = 1,
      .v = {0x06b8f59e, 0x43c0b2c2, 0x21052502, 0x217b5214},
      .key = {0x941709fd, 0xd8a25860, 0x861aecf3, 0x98a701a1, 0x0eb2c33b,
              0x74c08fad, 0x632d5227, 0x8c52f901},
      .instantiated = true,
      .fips_compliance = false,
  };
  csrng_testutils_kat_instantiate(csrng, fail_expected, &kEntropyInput,
                                  &kExpectedState);
}

void csrng_testutils_fips_generate_kat(const dif_csrng_t *csrng) {
  enum {
    kExpectedOutputLen = 16,
  };
  // TODO(#13342): csrng does not provide a linear output order. For example,
  // note the test vector output word order: 12,13,14,15 8,9,10,11 4,5,6,7
  // 0,1,2,3.
  const uint32_t kExpectedOutput[kExpectedOutputLen] = {
      0xe48bb8cb, 0x1012c84c, 0x5af8a7f1, 0xd1c07cd9, 0xdf82ab22, 0x771c619b,
      0xd40fccb1, 0x87189e99, 0x510494b3, 0x64f7ac0c, 0x2581f391, 0x80b1dc2f,
      0x793e01c5, 0x87b107ae, 0xdb17514c, 0xa43c41b7,
  };
  const dif_csrng_internal_state_t kExpectedState = {
      .reseed_counter = 3,
      .v = {0xe73e3392, 0x7d2e92b1, 0x1a0bac9d, 0x53c78ac6},
      .key = {0x66d1b85a, 0xc19d4dfd, 0x053b73e3, 0xe9dc0f90, 0x3f015bc8,
              0x4436e5fd, 0x1cccc697, 0x1a1c6e5f},
      .instantiated = true,
      .fips_compliance = false,
  };
  csrng_testutils_kat_generate(csrng, 2, kExpectedOutputLen, kExpectedOutput,
                               &kExpectedState);
}

void csrng_testutils_cmd_status_check(const dif_csrng_t *csrng) {
  dif_csrng_cmd_status_t status;
  CHECK_DIF_OK(dif_csrng_get_cmd_interface_status(csrng, &status));
  CHECK(status.errors == 0, "Unexpected CSRNG cmd interface error: 0x%x",
        status.errors);
  CHECK(status.unhealthy_fifos == 0, "Unexpected CSRNG FIFO error: 0x%x",
        status.unhealthy_fifos);
  CHECK(status.errors != kDifCsrngCmdStatusError,
        "Unexpected CSRNG status error");
}

void csrng_testutils_recoverable_alerts_check(const dif_csrng_t *csrng) {
  uint32_t alerts = UINT32_MAX;
  CHECK_DIF_OK(dif_csrng_get_recoverable_alerts(csrng, &alerts));
  CHECK(alerts == 0, "Unexpected local alerts 0x%x", alerts);
}
