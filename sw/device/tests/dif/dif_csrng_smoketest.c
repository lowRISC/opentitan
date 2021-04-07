// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

const test_config_t kTestConfig;

/**
 * FIPS CAVP test vector for CTR DRBG.
 *
 * CAVP test parameters.
 * Cipher: AES-256
 * Derivation Function: No
 * Prediction Resistance: False
 */
const dif_csrng_seed_material_t kEntropyInput = {
    .seed_material =
        {
            0xe4bc23c5,
            0x089a19d8,
            0x6f4119cb,
            0x3fa08c0a,
            0x4991e0a1,
            0xdef17e10,
            0x1e4c14d9,
            0xc323460a,
            0x7c2fb58e,
            0x0b086c6c,
            0x57b55f56,
            0xcae25bad,
        },
    .seed_material_len = 12,
};

/**
 * Expected CSRNG output.
 */
const uint32_t kExpectedOutput[] = {
    0xb2cb8905, 0xc05e5950, 0xca318950, 0x96be29ea, 0x3d5a3b82, 0xb2694955,
    0x54eb80fe, 0x07de43e1, 0x93b9e7c3, 0xece73b80, 0xe062b1c1, 0xf68202fb,
    0xb1c52a04, 0x0ea24788, 0x64295282, 0x234aaada,
};
const uint32_t kExpectedOutputLen = 16;

/**
 * Wait for the `csrng` instance command interface to be ready to
 * accept commands. Aborts test execution if an error is found.
 */
static void wait_for_csrng_cmd_ready(const dif_csrng_t *csrng) {
  dif_csrng_cmd_status_t cmd_status = {0};
  while (cmd_status != kDifCsrngCmdStatusReady) {
    CHECK(dif_csrng_get_cmd_interface_status(csrng, &cmd_status) ==
          kDifCsrngOk);
    CHECK(cmd_status != kDifCsrngCmdStatusError);
  }
}

/**
 * Run CAVP CTR DRBG Counter=0 with `kEntropyInput` deterministic
 * seed material.
 */
void test_ctr_drbg_ctr0(const dif_csrng_t *csrng) {
  wait_for_csrng_cmd_ready(csrng);
  CHECK(dif_csrng_instantiate(csrng, kDifCsrngEntropySrcToggleDisable,
                              &kEntropyInput) == kDifCsrngOk);

  wait_for_csrng_cmd_ready(csrng);
  const dif_csrng_seed_material_t seed_material = {0};
  CHECK(dif_csrng_reseed(csrng, &seed_material) == kDifCsrngOk);

  wait_for_csrng_cmd_ready(csrng);
  CHECK(dif_csrng_generate(csrng, kExpectedOutputLen) == kDifCsrngOk);

  dif_csrng_output_status_t output_status = {0};
  while (!output_status.valid_data) {
    CHECK(dif_csrng_get_output_status(csrng, &output_status) == kDifCsrngOk);
  }

  uint32_t output[16];
  CHECK(dif_csrng_read_output(csrng, output, kExpectedOutputLen) ==
        kDifCsrngOk);

  // TODO(#5982): Enable CSRNG SW path without entropy source.
  for (uint32_t i = 0; i < 16; ++i) {
    LOG_INFO("[%d] got = 0x%x; expected = 0x%x", i, output[i],
             kExpectedOutput[i]);
  }
}

bool test_main() {
  const dif_csrng_params_t params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR),
  };
  dif_csrng_t csrng;
  CHECK(dif_csrng_init(params, &csrng) == kDifCsrngOk);

  const dif_csrng_config_t config = {
      .debug_config = {.bypass_aes_cipher = false},
  };
  CHECK(dif_csrng_configure(&csrng, config) == kDifCsrngOk);

  test_ctr_drbg_ctr0(&csrng);

  return true;
}
