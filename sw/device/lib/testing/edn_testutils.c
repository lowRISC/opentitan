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
dif_edn_seed_material_t edn_testutils_seed_material_build(void) {
  dif_edn_seed_material_t seed;
  seed.len =
      rand_testutils_gen32_range(/*min=*/0, kDifEntropySeedMaterialMaxWordLen);
  for (size_t i = 0; i < seed.len; ++i) {
    seed.data[i] = rand_testutils_gen32();
  }
  return seed;
}

/**
 * Returns a randomized EDN auto mode configuration.
 */
dif_edn_auto_params_t edn_testutils_auto_params_build(void) {
  dif_edn_seed_material_t seed0 = edn_testutils_seed_material_build();
  dif_edn_seed_material_t seed1 = edn_testutils_seed_material_build();
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
                                            /*cmd_len=*/0,
                                            /*generate_len=*/1),
              .seed_material =
                  {
                      .len = 0,
                  },
          },
      .reseed_interval = 4,
  };
}
