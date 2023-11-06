// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/edn_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/rv_core_ibex_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "edn_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  kEdnKatTimeout = (10 * 1000 * 1000),
  kEdnKatMaxClen = 12,
  kEdnKatOutputLen = 16,
  kEdnKatWordsPerBlock = 4,
};

static dif_entropy_src_t entropy_src;
static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;
static dif_rv_core_ibex_t rv_core_ibex;

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

// Seed material for the EDN KAT instantiate command.
const dif_edn_seed_material_t kEdnKatSeedMaterialInstantiate = {
    .len = kEdnKatMaxClen,
    .data = {0x73bec010, 0x9262474c, 0x16a30f76, 0x531b51de, 0x2ee494e5,
             0xdfec9db3, 0xcb7a879d, 0x5600419c, 0xca79b0b0, 0xdda33b5c,
             0xa468649e, 0xdf5d73fa},
};
// Seed material for the EDN KAT reseed command.
const dif_edn_seed_material_t kEdnKatSeedMaterialReseed = {
    .len = kEdnKatMaxClen,
    .data = {0x73bec010, 0x9262474c, 0x16a30f76, 0x531b51de, 0x2ee494e5,
             0xdfec9db3, 0xcb7a879d, 0x5600419c, 0xca79b0b0, 0xdda33b5c,
             0xa468649e, 0xdf5d73fa},
};
// Seed material for the EDN KAT generate command.
const dif_edn_seed_material_t kEdnKatSeedMaterialGenerate = {
    .len = 0,
};
// Expected output data for the EDN KAT.
const uint32_t kExpectedOutput[kEdnKatOutputLen] = {
    0xe48bb8cb, 0x1012c84c, 0x5af8a7f1, 0xd1c07cd9, 0xdf82ab22, 0x771c619b,
    0xd40fccb1, 0x87189e99, 0x510494b3, 0x64f7ac0c, 0x2581f391, 0x80b1dc2f,
    0x793e01c5, 0x87b107ae, 0xdb17514c, 0xa43c41b7,
};

// Seed material for the edn alert part of this test. The CTR_DRBG construction
// implemented by CSRNG produces
//
// key = 00 01 02 03 04 05 06 07 - 08 09 0a 0b 0c 0d 0e 0f
//       10 11 12 13 14 15 16 17 - 18 19 1a 1b 1c 1d 1e 1f
//
//   V = 8d 97 b4 1b c2 0a cb bb - 81 06 d3 91 85 46 67 f8
//
// from this seed material upon instantiate. The key is arbitrarily chosen.
// Encrypting V using this key then gives the required output seed. This seed
// material was taken from aes_testutils.c.

// Seed material for the EDN alert test instantiate command.
const dif_edn_seed_material_t kEdnAlertTestSeedMaterialInstantiate = {
    .len = kEdnKatMaxClen,
    .data = {0xf0405279, 0x50a4261f, 0xf5ace1cf, 0xfff7b7d1, 0xa6ee8307,
             0x1f57dfc8, 0x59757d79, 0xdeb6522e, 0xc8c67d84, 0xa16abefa,
             0xc34030be, 0x530e88f8},
};
// Seed material for reseed command. After one generate, this seed material
// will bring the key and V of CSRNG back to the state after instantiate.
const dif_edn_seed_material_t kEdnAlertTestSeedMaterialReseed = {
    .len = kEdnKatMaxClen,
    .data = {0x5f6fb665, 0x21ca8e3f, 0x5ba3dba1, 0x2c10a9ec, 0x03b8cd4b,
             0x8264aaea, 0x371e6305, 0x8fb186e1, 0xf622bc3e, 0x98e5d247,
             0x73040c38, 0x6596739e},
};

OTTF_DEFINE_TEST_CONFIG();

// Initializes the peripherals used in this test.
static void init_peripherals(void) {
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  CHECK_DIF_OK(dif_csrng_init(
      mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn1));
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));
}

dif_edn_auto_params_t kat_auto_params_build(bool alert_test) {
  return (dif_edn_auto_params_t){
      .instantiate_cmd =
          {
              .cmd = csrng_cmd_header_build(
                  kCsrngAppCmdInstantiate, kDifCsrngEntropySrcToggleDisable,
                  alert_test ? kEdnAlertTestSeedMaterialInstantiate.len
                             : kEdnKatSeedMaterialInstantiate.len,
                  /*generate_len=*/0),
              .seed_material = alert_test ? kEdnAlertTestSeedMaterialInstantiate
                                          : kEdnKatSeedMaterialInstantiate,
          },
      .reseed_cmd =
          {
              .cmd = csrng_cmd_header_build(
                  kCsrngAppCmdReseed, kDifCsrngEntropySrcToggleDisable,
                  alert_test ? kEdnAlertTestSeedMaterialReseed.len
                             : kEdnKatSeedMaterialReseed.len,
                  /*generate_len=*/0),
              .seed_material = alert_test ? kEdnAlertTestSeedMaterialReseed
                                          : kEdnKatSeedMaterialReseed,
          },
      .generate_cmd =
          {
              .cmd = csrng_cmd_header_build(
                  kCsrngAppCmdGenerate, kDifCsrngEntropySrcToggleDisable,
                  kEdnKatSeedMaterialGenerate.len,
                  /*generate_len=*/
                  alert_test ? 1 : kEdnKatOutputLen / kEdnKatWordsPerBlock),
              .seed_material = kEdnKatSeedMaterialGenerate,
          },
      .reseed_interval = alert_test ? 1 : 32,
  };
}

static uint32_t ibex_get_rnd_data(void) {
  uint32_t ibex_rnd_data;
  CHECK_STATUS_OK(rv_core_ibex_testutils_get_rnd_data(
      &rv_core_ibex, kEdnKatTimeout, &ibex_rnd_data));
  return ibex_rnd_data;
}

// Configure the entropy complex.
static void entropy_config(bool alert_test) {
  dif_edn_auto_params_t edn_params =
      edn_testutils_auto_params_build(true, /*res_itval=*/0, /*glen_val=*/0);
  // Disable the entropy complex.
  CHECK_STATUS_OK(entropy_testutils_stop_all());
  // Enable ENTROPY_SRC in FIPS mode.
  CHECK_DIF_OK(dif_entropy_src_configure(
      &entropy_src, entropy_testutils_config_default(), kDifToggleEnabled));
  // Enable CSRNG.
  CHECK_DIF_OK(dif_csrng_configure(&csrng));
  // Enable EDN1 in auto request mode.
  CHECK_DIF_OK(dif_edn_set_auto_mode(&edn1, edn_params));
  // Enable EDN0 in auto request mode.
  CHECK_DIF_OK(dif_edn_set_auto_mode(&edn0, kat_auto_params_build(alert_test)));
}

static bool execute_kat(void) {
  uint32_t ibex_rnd_data_got;
  unsigned int next_val_pos = 0;
  unsigned int hits = 0;

  // kExpectedOutput contains kEdnKatOutputLen precalculated words of the
  // expected random output. The EDN might hold some buffered words from
  // previous instantiations of the entropy complex. Since there are other
  // blocks that consume entropy in between ibex rnd data requests, the first
  // hit might not be the first word in the expected sequence. The following
  // hits might also skip some words in the expected sequence if random words
  // have been stolen by other blocks.
  while (next_val_pos < kEdnKatOutputLen) {
    // Fetch a new word of random bits.
    ibex_rnd_data_got = ibex_get_rnd_data();
    // Iterate over the remaining words in the expected sequence.
    for (unsigned int i = next_val_pos; i < kEdnKatOutputLen; ++i) {
      // If there is a hit, the next potential hit is the current position +1.
      if (ibex_rnd_data_got == kExpectedOutput[i]) {
        next_val_pos = i + 1;
        hits++;
        break;
        // If the first hit has happened and there is no hit in this position,
        // this word has been stolen by another block. Thus, we need to
        // increment the potential next_val_pos.
      } else if (hits) {
        next_val_pos = i + 1;
      }
    }
  }
  // If less than half of the words in the expected sequence were hit throw an
  // exception.
  LOG_INFO("%d/%d expected random words have been hit.", hits,
           kEdnKatOutputLen);
  CHECK(hits >= kEdnKatOutputLen / 2);
  return true;
}

static void execute_alert_test(void) {
  uint32_t alerts;
  for (int i = 0; i <= 2 * kEdnKatWordsPerBlock; ++i) {
    ibex_get_rnd_data();
  }
  CHECK_DIF_OK(dif_edn_get_recoverable_alerts(&edn0, &alerts));
  CHECK((alerts >> kDifEdnRecoverableAlertRepeatedGenBits) & 0x1);
}

bool test_main(void) {
  LOG_INFO("init_peripherals start");
  init_peripherals();
  // Verify that EDN0 delivers the expected entropy bits using the
  // rv_core_ibex.RND_DATA and rv_core_ibex.RND_STATUS registers.
  entropy_config(/*alert_test=*/false);
  IBEX_SPIN_FOR(execute_kat(), kEdnKatTimeout);
  // Verify that EDN0 sets the RECOV_ALERT_STS.EDN_BUS_CMP_ALERT bit as CSRNG
  // continues to provide the same entropy bits to EDN0.
  entropy_config(/*alert_test=*/true);
  execute_alert_test();

  return true;
}
