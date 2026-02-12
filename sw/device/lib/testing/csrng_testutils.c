// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/csrng_testutils.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top/csrng_regs.h"  // Generated

#define MODULE_ID MAKE_MODULE_ID('r', 'n', 't')

enum {
  kNumOutputWordsMax = 16,
};

/**
 * Generates randomized seed material.
 */
status_t csrng_testutils_seed_material_build(
    bool disable_rand, dif_csrng_seed_material_t *seed_material) {
  if (seed_material == NULL) {
    return INVALID_ARGUMENT();
  }
  seed_material->seed_material_len =
      disable_rand
          ? 0
          : rand_testutils_gen32_range(0, kDifCsrngSeedMaterialMaxWordLen);
  for (size_t i = 0; i < seed_material->seed_material_len; ++i) {
    seed_material->seed_material[i] = rand_testutils_gen32();
  }
  return OK_STATUS();
}

/**
 * Returns a randomized CSRNG application command.
 */
csrng_app_cmd_t csrng_testutils_app_cmd_build(
    bool disable_rand, csrng_app_cmd_id_t id,
    dif_csrng_entropy_src_toggle_t entropy_src_en, unsigned int glen_val,
    dif_csrng_seed_material_t *seed_material) {
  CHECK_STATUS_OK(
      csrng_testutils_seed_material_build(disable_rand, seed_material));

  // If disable_rand is true, we set flag0 to the provided value.
  // If disable_rand is false, we pick a value at random.
  dif_csrng_entropy_src_toggle_t entropy_src_enable =
      disable_rand                       ? entropy_src_en
      : rand_testutils_gen32_range(0, 1) ? kDifCsrngEntropySrcToggleEnable
                                         : kDifCsrngEntropySrcToggleDisable;

  // If glen_val > 0, the generate length is set to glen_val.
  // If disable_rand is false we pick a random value between 1 and 10 with a
  // bias towards 1. Otherwise, if glen would be too high, we would not see
  // any reseeds because we do not consume enough entropy.
  unsigned int glen = glen_val ? glen_val
                      : (disable_rand || rand_testutils_gen32_range(0, 1))
                          ? 1
                          : rand_testutils_gen32_range(2, 10);

  return (csrng_app_cmd_t){
      .id = id,
      .entropy_src_enable = entropy_src_enable,
      .seed_material = seed_material,
      .generate_len = glen,
  };
}

status_t csrng_testutils_cmd_ready_wait(const dif_csrng_t *csrng) {
  dif_csrng_cmd_status_t cmd_status;
  do {
    TRY(dif_csrng_get_cmd_interface_status(csrng, &cmd_status));
    TRY_CHECK(cmd_status.kind != kDifCsrngCmdStatusError);
  } while (cmd_status.kind != kDifCsrngCmdStatusReady);
  return OK_STATUS();
}

status_t csrng_testutils_cmd_generate_run(
    const dif_csrng_t *csrng, const dif_csrng_seed_material_t *additional_data,
    uint32_t *output, size_t output_len) {
  TRY(csrng_testutils_cmd_ready_wait(csrng));
  TRY(dif_csrng_generate_start(csrng, additional_data, output_len));

  dif_csrng_output_status_t output_status;
  do {
    TRY(dif_csrng_get_output_status(csrng, &output_status));
  } while (!output_status.valid_data);

  TRY(dif_csrng_generate_read(csrng, output, output_len));
  return OK_STATUS();
}

status_t csrng_testutils_check_internal_state(
    const dif_csrng_t *csrng, const dif_csrng_internal_state_t *expected) {
  TRY(csrng_testutils_cmd_ready_wait(csrng));
  dif_csrng_internal_state_t got;
  TRY(dif_csrng_get_internal_state(csrng, kCsrngInternalStateIdSw, &got));
  uint32_t reseed_counter;
  TRY(dif_csrng_get_reseed_counter(csrng, kCsrngInternalStateIdSw,
                                   &reseed_counter));

  TRY_CHECK(got.instantiated == expected->instantiated);
  TRY_CHECK(got.reseed_counter == expected->reseed_counter);
  TRY_CHECK(reseed_counter == expected->reseed_counter);
  TRY_CHECK(got.fips_compliance == expected->fips_compliance);

  TRY_CHECK(memcmp(got.v, expected->v, sizeof(expected->v)) == 0);

  TRY_CHECK(memcmp(got.key, expected->key, sizeof(expected->key)) == 0);
  return OK_STATUS();
}

status_t csrng_testutils_kat_instantiate(
    const dif_csrng_t *csrng, bool fail_expected,
    const dif_csrng_seed_material_t *seed_material,
    const dif_csrng_internal_state_t *expected_state) {
  LOG_INFO("CSRNG KAT instantiate");
  TRY(csrng_testutils_cmd_ready_wait(csrng));
  TRY(dif_csrng_uninstantiate(csrng));

  // Instantiate CSRNG - use the provided seed material only.
  TRY(csrng_testutils_cmd_ready_wait(csrng));
  TRY(dif_csrng_instantiate(csrng, kDifCsrngEntropySrcToggleDisable,
                            seed_material));

  // Check the internal state of created CSRNG instance.
  dif_csrng_internal_state_t zero_state;
  memset(&zero_state, 0, sizeof(zero_state));
  return csrng_testutils_check_internal_state(
      csrng, fail_expected ? &zero_state : expected_state);
}

status_t csrng_testutils_kat_generate(
    const dif_csrng_t *csrng, size_t num_generates, size_t output_len,
    const dif_csrng_seed_material_t *additional_data,
    const uint32_t *expected_output,
    const dif_csrng_internal_state_t *expected_state) {
  LOG_INFO("CSRNG KAT generate");

  // Run the generate and check the output.
  uint32_t got[kNumOutputWordsMax];
  for (int i = 0; i < num_generates; ++i) {
    TRY(csrng_testutils_cmd_generate_run(csrng, additional_data, got,
                                         output_len));
  }

  if (expected_output != NULL) {
    TRY_CHECK(memcmp(got, expected_output, output_len) == 0);
  }

  // Check the internal state.
  return csrng_testutils_check_internal_state(csrng, expected_state);
}

status_t csrng_testutils_kat_reseed(
    const dif_csrng_t *csrng, const dif_csrng_seed_material_t *seed_material,
    const dif_csrng_internal_state_t *expected_state) {
  LOG_INFO("CSRNG KAT reseed");

  // Reseed CSRNG - use the provided seed material only.
  TRY(csrng_testutils_cmd_ready_wait(csrng));
  TRY(csrng_send_app_cmd(
      csrng->base_addr, kCsrngAppCmdTypeCsrng,
      (csrng_app_cmd_t){
          .id = kCsrngAppCmdReseed,
          .entropy_src_enable = kDifCsrngEntropySrcToggleDisable,
          .seed_material = seed_material,
      }));

  // Check the internal state.
  return csrng_testutils_check_internal_state(csrng, expected_state);
}

status_t csrng_testutils_fips_instantiate_kat(const dif_csrng_t *csrng,
                                              bool fail_expected) {
  // CTR_DRBG Known-Answer-Tests (KATs).
  //
  // Test vector sourced from NIST's CAVP website:
  // https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/random-number-generators
  //
  // The number format in this docstring follows the CAVP format to simplify
  // auditing of this test case.
  //
  // Test vector: CTR_DRBG AES-256 no DF from
  // drbgvectors_no_reseed.zip/CTR_DRBG.txt with parameters
  // - PredictionResistance = False
  // - EntropyInputLen = 384
  // - NonceLen = 0
  // - PersonalizationStringLen = 0
  // - AdditionalInputLen = 0
  // - ReturnedBitsLen = 512
  // - COUNT = 0
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
      .reseed_counter = 0,
      .v = {0x06b8f59e, 0x43c0b2c2, 0x21052502, 0x217b5214},
      .key = {0x941709fd, 0xd8a25860, 0x861aecf3, 0x98a701a1, 0x0eb2c33b,
              0x74c08fad, 0x632d5227, 0x8c52f901},
      .instantiated = true,
      .fips_compliance = false,
  };
  return csrng_testutils_kat_instantiate(csrng, fail_expected, &kEntropyInput,
                                         &kExpectedState);
}

status_t csrng_testutils_fips_generate_kat(const dif_csrng_t *csrng) {
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
      .reseed_counter = 2,
      .v = {0xe73e3392, 0x7d2e92b1, 0x1a0bac9d, 0x53c78ac6},
      .key = {0x66d1b85a, 0xc19d4dfd, 0x053b73e3, 0xe9dc0f90, 0x3f015bc8,
              0x4436e5fd, 0x1cccc697, 0x1a1c6e5f},
      .instantiated = true,
      .fips_compliance = false,
  };
  return csrng_testutils_kat_generate(csrng, 2, kExpectedOutputLen, NULL,
                                      kExpectedOutput, &kExpectedState);
}

status_t csrng_testutils_fips_instantiate_kat_adata(const dif_csrng_t *csrng,
                                                    bool fail_expected) {
  // CTR_DRBG Known-Answer-Tests (KATs).
  //
  // Test vector sourced from NIST's CAVP website:
  // https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/random-number-generators
  //
  // The number format in this docstring follows the CAVP format to simplify
  // auditing of this test case.
  //
  // Test vector: CTR_DRBG AES-256 no DF from
  // drbgvectors_no_reseed.zip/CTR_DRBG.txt with parameters
  // - PredictionResistance = False
  // - EntropyInputLen = 384
  // - NonceLen = 0
  // - PersonalizationStringLen = 0
  // - AdditionalInputLen = 384
  // - ReturnedBitsLen = 512
  // - COUNT = 0
  //
  // - EntropyInput =
  // f45e9d040c1456f1c7f26e7f146469fbe3973007fe037239ad57623046e7ec52221b22eec208b22ac4cf4ca8d6253874
  // - Nonce = EMPTY
  // - PersonalizationString = EMPTY
  //
  // Command: Instantiate
  // - Key = a75117ffcb5160486e91da8ed0af1a702d30703ab3631957aa19a7e3fc14714a
  // - V   = 507b2124f5ae985e156db926a3230dfa
  //
  // - AdditionalInput =
  // 28819bc79b92fc8790ebdc99812cdcea5c96e6feab32801ec1851b9f46e80eb6800028e61fbccb6ccbe42b06bf5a0864
  // Command: Generate (first call):
  // - Key = d75e41010982abd243b4d75642b86ce07e13b3652a3725aad011b1097c32957a
  // - V   = 939fbb584e0103982d2e73e05779849f
  //
  // - AdditionalInput =
  // 418ca848027e1b3c84d66717e6f31bf89684d5db94cd2d579233f716ac70ab66cc7b01a6f9ab8c7665fcc37dba4af1ad
  // Command: Generate (second call):
  // - Key = b0f80df4b33e5d2e3d72c8667ba9da1aa64a3a4936a3fdabf2c980d3104dfa13
  // - V   = 433abd3907feddce66cbcb216d5d833e
  // - ReturnedBits =
  // 4f11406bd303c104243441a8f828bf0293cb20ac39392061429c3f56c1f426239f8f0c687b69897a2c7c8c2b4fb520b62741ffdd29f038b7c82a9d00a890a3ed

  const dif_csrng_seed_material_t kEntropyInput = {
      .seed_material = {0xd6253874, 0xc4cf4ca8, 0xc208b22a, 0x221b22ee,
                        0x46e7ec52, 0xad576230, 0xfe037239, 0xe3973007,
                        0x146469fb, 0xc7f26e7f, 0x0c1456f1, 0xf45e9d04},
      .seed_material_len = 12,
  };
  const dif_csrng_internal_state_t kExpectedState = {
      .reseed_counter = 0,
      .v = {0xa3230dfa, 0x156db926, 0xf5ae985e, 0x507b2124},
      .key = {0xfc14714a, 0xaa19a7e3, 0xb3631957, 0x2d30703a, 0xd0af1a70,
              0x6e91da8e, 0xcb516048, 0xa75117ff},
      .instantiated = true,
      .fips_compliance = false,
  };
  return csrng_testutils_kat_instantiate(csrng, fail_expected, &kEntropyInput,
                                         &kExpectedState);
}

status_t csrng_testutils_fips_generate_kat_adata1(const dif_csrng_t *csrng) {
  enum {
    kExpectedOutputLen = 16,
  };
  const dif_csrng_seed_material_t kAdditionalData = {
      .seed_material = {0xbf5a0864, 0xcbe42b06, 0x1fbccb6c, 0x800028e6,
                        0x46e80eb6, 0xc1851b9f, 0xab32801e, 0x5c96e6fe,
                        0x812cdcea, 0x90ebdc99, 0x9b92fc87, 0x28819bc7},
      .seed_material_len = 12,
  };
  const dif_csrng_internal_state_t kExpectedState = {
      .reseed_counter = 1,
      .v = {0x5779849f, 0x2d2e73e0, 0x4e010398, 0x939fbb58},
      .key = {0x7c32957a, 0xd011b109, 0x2a3725aa, 0x7e13b365, 0x42b86ce0,
              0x43b4d756, 0x0982abd2, 0xd75e4101},
      .instantiated = true,
      .fips_compliance = false,
  };
  return csrng_testutils_kat_generate(csrng, 1, kExpectedOutputLen,
                                      &kAdditionalData, NULL, &kExpectedState);
}

status_t csrng_testutils_fips_generate_kat_adata2(const dif_csrng_t *csrng) {
  enum {
    kExpectedOutputLen = 16,
  };
  const dif_csrng_seed_material_t kAdditionalData = {
      .seed_material = {0xba4af1ad, 0x65fcc37d, 0xf9ab8c76, 0xcc7b01a6,
                        0xac70ab66, 0x9233f716, 0x94cd2d57, 0x9684d5db,
                        0xe6f31bf8, 0x84d66717, 0x027e1b3c, 0x418ca848},
      .seed_material_len = 12,
  };
  // TODO(#13342): csrng does not provide a linear output order. For example,
  // note the test vector output word order: 12,13,14,15 8,9,10,11 4,5,6,7
  // 0,1,2,3.
  const uint32_t kExpectedOutput[kExpectedOutputLen] = {
      0xf828bf02, 0x243441a8, 0xd303c104, 0x4f11406b, 0xc1f42623, 0x429c3f56,
      0x39392061, 0x93cb20ac, 0x4fb520b6, 0x2c7c8c2b, 0x7b69897a, 0x9f8f0c68,
      0xa890a3ed, 0xc82a9d00, 0x29f038b7, 0x2741ffdd};
  const dif_csrng_internal_state_t kExpectedState = {
      .reseed_counter = 2,
      .v = {0x6d5d833e, 0x66cbcb21, 0x07feddce, 0x433abd39},
      .key = {0x104dfa13, 0xf2c980d3, 0x36a3fdab, 0xa64a3a49, 0x7ba9da1a,
              0x3d72c866, 0xb33e5d2e, 0xb0f80df4},
      .instantiated = true,
      .fips_compliance = false,
  };
  return csrng_testutils_kat_generate(csrng, 1, kExpectedOutputLen,
                                      &kAdditionalData, kExpectedOutput,
                                      &kExpectedState);
}

status_t csrng_testutils_cmd_status_check(const dif_csrng_t *csrng) {
  dif_csrng_cmd_status_t status;
  TRY(dif_csrng_get_cmd_interface_status(csrng, &status));
  TRY_CHECK(status.cmd_sts == kDifCsrngCmdStsSuccess);
  return OK_STATUS();
}

status_t csrng_testutils_recoverable_alerts_check(const dif_csrng_t *csrng) {
  uint32_t alerts = UINT32_MAX;
  TRY(dif_csrng_get_recoverable_alerts(csrng, &alerts));
  TRY_CHECK(alerts == 0);
  return OK_STATUS();
}
