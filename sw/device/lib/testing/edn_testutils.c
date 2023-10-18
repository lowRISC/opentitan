// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/edn_testutils.h"

#include "sw/device/lib/dif/dif_csrng_shared.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/testing/rand_testutils.h"

/**
 * Returns randomized seed material.
 */
dif_edn_seed_material_t edn_testutils_seed_material_build(bool disable_rand) {
  dif_edn_seed_material_t seed;
  seed.len = disable_rand ? 0
                          : rand_testutils_gen32_range(
                                0, kDifEntropySeedMaterialMaxWordLen);
  for (size_t i = 0; i < seed.len; ++i) {
    seed.data[i] = rand_testutils_gen32();
  }
  return seed;
}

/**
 * Returns a randomized EDN auto mode configuration.
 */
dif_edn_auto_params_t edn_testutils_auto_params_build(bool disable_rand) {
  dif_edn_seed_material_t seed0 =
      edn_testutils_seed_material_build(disable_rand);
  dif_edn_seed_material_t seed1 =
      edn_testutils_seed_material_build(disable_rand);
  dif_edn_seed_material_t seed2 =
      edn_testutils_seed_material_build(disable_rand);
  // If disable_rand is true we set the glen to the default 1.
  // If disable_rand is false we pick a random value between 1 and 10 with a
  // bias towards 1. Otherwise, if glen would be too high, we would not see
  // any reseeds because we do not consume enough entropy.
  unsigned int glen = (disable_rand || rand_testutils_gen32_range(0, 1))
                          ? 1
                          : rand_testutils_gen32_range(2, 10);
  // The same goes for the number of requests between reseeds
  unsigned int num_reqs_between_reseeds =
      (disable_rand || rand_testutils_gen32_range(0, 1))
          ? 1
          : rand_testutils_gen32_range(2, 5);

  return (dif_edn_auto_params_t){
      .instantiate_cmd =
          {
              .cmd = csrng_cmd_header_build(kCsrngAppCmdInstantiate,
                                            kDifCsrngEntropySrcToggleEnable,
                                            seed0.len,
                                            /*generate_len=*/0),
              .seed_material = seed0,
          },
      .reseed_cmd =
          {
              .cmd = csrng_cmd_header_build(kCsrngAppCmdReseed,
                                            kDifCsrngEntropySrcToggleEnable,
                                            seed1.len,
                                            /*generate_len=*/0),
              .seed_material = seed1,
          },
      .generate_cmd =
          {
              .cmd = csrng_cmd_header_build(kCsrngAppCmdGenerate,
                                            kDifCsrngEntropySrcToggleEnable,
                                            seed2.len, glen),
              .seed_material = seed2,
          },
      .reseed_interval = num_reqs_between_reseeds,
  };
}
