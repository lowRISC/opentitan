// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/aes_testutils.h"

#if !OT_IS_ENGLISH_BREAKFAST
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/testing/csrng_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "csrng_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#endif

// `extern` declarations to give the inline functions in the
// corresponding header a link location.

extern bool aes_testutils_get_status(dif_aes_t *aes, dif_aes_status_t flag);

#if !OT_IS_ENGLISH_BREAKFAST
/**
 * Constants for switching AES masking off.
 */
enum {
  kCsrngBlockLen = 4,
  kCsrngKeyLen = 8,
  kEdnSeedMaterialLen = 12,
};

// CSRNG needs to constantly output these bits to EDN. The AES masking PRNG
// consists of five 32-bit LFSRs each followed by a linear permutation and a
// non-linear layer and ultimately a secret permutation spanning all five
// LFSRs. Only if the non-linear layers of all five LFSRs output an all-zero
// vector, the PRNG output is zero as well.
//
const uint32_t kAesMaskingPrngZeroOutputSeed[kCsrngBlockLen] = {
    0xff00ffff, 0xff00ffff, 0xff00ffff, 0xff00ffff};

// Seed material for instantiate command. The CTR_DRBG construction
// implemented by CSRNG produces
//
// key = 00 01 02 03 04 05 06 07 - 08 09 0a 0b 0c 0d 0e 0f
//       10 11 12 13 14 15 16 17 - 18 19 1a 1b 1c 1d 1e 1f
//
//   V = 8d 97 b4 1b c2 0a cb bb - 81 06 d3 91 85 46 67 f8
//
// from this seed material upon instantiate. The key is arbitrarily chosen.
// Encrypting V using this key then gives the required
// kAesMaskingPrngZeroOutputSeed above.
const uint32_t kEdnSeedMaterialInstantiate[kEdnSeedMaterialLen] = {
    0xf0405279, 0x50a4261f, 0xf5ace1cf, 0xfff7b7d1, 0xa6ee8307, 0x1f57dfc8,
    0x59757d79, 0xdeb6522e, 0xc8c67d84, 0xa16abefa, 0xc34030be, 0x530e88f8};

// V and key after instantiate.
const uint32_t kCsrngVInstantiate[kCsrngBlockLen] = {0x854667f7, 0x8106d391,
                                                     0xc20acbbb, 0x8d97b41b};
const uint32_t kCsrngKeyInstantiate[kCsrngKeyLen] = {
    0x1c1d1e1f, 0x18191a1b, 0x14151617, 0x10111213,
    0x0c0d0e0f, 0x08090a0b, 0x04050607, 0x00010203};

// V and key after generate.
const uint32_t kCsrngVGenerate[kCsrngBlockLen] = {0x1569e491, 0xe854f642,
                                                  0xe931a570, 0x60939074};
const uint32_t kCsrngKeyGenerate[kCsrngKeyLen] = {
    0xfdab6b68, 0x31920240, 0x32a48b64, 0xda4189d7,
    0xf49b7a55, 0x3d86fe43, 0xf4eaeab1, 0x8fae023a};

// Seed material for reseed command. After one generate, this seed material
// will bring the key and V of CSRNG back to the state after instantiate.
// I.e., one can again run one generate to produce the seed required for AES
// (see kAesMaskingPrngZeroOutputSeed).
const uint32_t kEdnSeedMaterialReseed[kEdnSeedMaterialLen] = {
    0x5f6fb665, 0x21ca8e3f, 0x5ba3dba1, 0x2c10a9ec, 0x03b8cd4b, 0x8264aaea,
    0x371e6305, 0x8fb186e1, 0xf622bc3e, 0x98e5d247, 0x73040c38, 0x6596739e};

status_t aes_testutils_masking_prng_zero_output_seed(void) {
  const dif_csrng_t csrng = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR)};
  const dif_edn_t edn0 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR)};

  // Shutdown EDN0 and CSRNG
  TRY(dif_edn_stop(&edn0));
  TRY(dif_csrng_stop(&csrng));

  // Re-eanble CSRNG
  TRY(dif_csrng_configure(&csrng));

  // Re-enable EDN0 and configure it to produce the seed that if loaded into AES
  // causes the AES masking PRNG to output and all-zero output.
  dif_edn_auto_params_t edn0_params = {
      .instantiate_cmd =
          {
              .cmd = csrng_cmd_header_build(kCsrngAppCmdInstantiate,
                                            kDifCsrngEntropySrcToggleDisable,
                                            kEdnSeedMaterialLen,
                                            /*generate_len=*/0),
              .seed_material =
                  {
                      .len = kEdnSeedMaterialLen,
                  },
          },
      .reseed_cmd =
          {
              .cmd = csrng_cmd_header_build(kCsrngAppCmdReseed,
                                            kDifCsrngEntropySrcToggleDisable,
                                            kEdnSeedMaterialLen,
                                            /*generate_len=*/0),
              .seed_material =
                  {
                      .len = kEdnSeedMaterialLen,
                  },
          },
      .generate_cmd =
          {
              .cmd = csrng_cmd_header_build(kCsrngAppCmdGenerate,
                                            kDifCsrngEntropySrcToggleDisable,
                                            /*cmd_len=*/0,
                                            /*generate_len=*/1),
              .seed_material =
                  {
                      .len = 0,
                  },
          },
      .reseed_interval = 1,  // Reseed after every single generate.
  };
  memcpy(edn0_params.instantiate_cmd.seed_material.data,
         kEdnSeedMaterialInstantiate, sizeof(kEdnSeedMaterialInstantiate));
  memcpy(edn0_params.reseed_cmd.seed_material.data, kEdnSeedMaterialReseed,
         sizeof(kEdnSeedMaterialReseed));
  TRY(dif_edn_set_auto_mode(&edn0, edn0_params));
  return OK_STATUS();
}

status_t aes_testutils_csrng_kat(void) {
  const dif_csrng_t csrng = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR)};

  // Instantiate CSRNG with seed material suitable for switching the AES masking
  // off.
  dif_csrng_seed_material_t seed_material_instantiate = {
      .seed_material_len = 12,
  };
  memcpy(seed_material_instantiate.seed_material, kEdnSeedMaterialInstantiate,
         sizeof(kEdnSeedMaterialInstantiate));
  dif_csrng_internal_state_t expected_state_instantiate = {
      .reseed_counter = 1,
      .instantiated = true,
      .fips_compliance = false,
  };
  memcpy(expected_state_instantiate.v, kCsrngVInstantiate,
         sizeof(kCsrngVInstantiate));
  memcpy(expected_state_instantiate.key, kCsrngKeyInstantiate,
         sizeof(kCsrngKeyInstantiate));
  TRY(csrng_testutils_kat_instantiate(&csrng, false, &seed_material_instantiate,
                                      &expected_state_instantiate));

  // Generate one block containing the required seed for the AES masking PRNG
  // to output an all-zero vector.
  dif_csrng_internal_state_t expected_state_generate = {
      .reseed_counter = 2,
      .instantiated = true,
      .fips_compliance = false,
  };
  memcpy(expected_state_generate.v, kCsrngVGenerate, sizeof(kCsrngVGenerate));
  memcpy(expected_state_generate.key, kCsrngKeyGenerate,
         sizeof(kCsrngKeyGenerate));
  TRY(csrng_testutils_kat_generate(&csrng, 1, kCsrngBlockLen,
                                   kAesMaskingPrngZeroOutputSeed,
                                   &expected_state_generate));

  // Reseed the CSRNG instance to produce the required seed for the AES masking
  // PRNG to output an all-zero vector upon the next generate command.
  dif_csrng_seed_material_t seed_material_reseed = {
      .seed_material_len = 12,
  };
  memcpy(seed_material_reseed.seed_material, kEdnSeedMaterialReseed,
         sizeof(kEdnSeedMaterialReseed));
  dif_csrng_internal_state_t expected_state_reseed = {
      .reseed_counter = 1,
      .instantiated = true,
      .fips_compliance = false,
  };
  memcpy(expected_state_reseed.v, kCsrngVInstantiate,
         sizeof(kCsrngVInstantiate));
  memcpy(expected_state_reseed.key, kCsrngKeyInstantiate,
         sizeof(kCsrngKeyInstantiate));
  TRY(csrng_testutils_kat_reseed(&csrng, &seed_material_reseed,
                                 &expected_state_reseed));

  // Generate one block containing the required seed for the AES masking PRNG
  // to output an all-zero vector.
  TRY(csrng_testutils_kat_generate(&csrng, 1, kCsrngBlockLen,
                                   kAesMaskingPrngZeroOutputSeed,
                                   &expected_state_generate));
  return OK_STATUS();
}
#endif
