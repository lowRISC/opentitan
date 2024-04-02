// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/edn_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/rv_core_ibex_testutils.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/tests/crypto/cryptotest/firmware/sca_lib.h"
#include "sw/device/tests/crypto/cryptotest/json/edn_fi_commands.h"

#include "edn_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// NOP macros.
#define NOP1 "addi x0, x0, 0\n"
#define NOP10 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1

enum {
  kEdnKatTimeout = (10 * 1000 * 1000),
  kEdnKatMaxClen = 12,
  kEdnKatOutputLen = 16,
  kEdnKatWordsPerBlock = 4,
};

static dif_rv_core_ibex_t rv_core_ibex;
static dif_entropy_src_t entropy_src;
static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;

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

status_t handle_edn_fi_bus_ack(ujson_t *uj) {
  // Enable entropy complex, CSRNG and EDN so Ibex can get entropy.
  // Configure entropy in auto_mode to avoid starving the system from entropy,
  // given that boot mode entropy has a limited number of generated bits.
  TRY(entropy_testutils_auto_mode_init());

  uint32_t ibex_rnd_data[64];

  // Inject faults during generating and receiving random data.
  // Goal is to manipulate ACK on bus to trigger that the same
  // data chunk is transmitted multiple times.
  sca_set_trigger_high();
  asm volatile(NOP10);
  for (size_t it = 0; it < 64; it++) {
    TRY(rv_core_ibex_testutils_get_rnd_data(&rv_core_ibex, kEdnKatTimeout,
                                            &ibex_rnd_data[it]));
  }
  sca_set_trigger_low();

  // Check if there are any collisions.
  size_t collisions = 0;
  for (size_t outer = 0; outer < 64; outer++) {
    for (size_t inner = 0; inner < 64; inner++) {
      if (outer != inner) {
        if (ibex_rnd_data[outer] == ibex_rnd_data[inner]) {
          collisions++;
        }
      }
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send result & ERR_STATUS to host.
  edn_fi_test_result_t uj_output;
  uj_output.result = collisions;
  uj_output.err_status = codes;
  RESP_OK(ujson_serialize_edn_fi_test_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_edn_fi_bus_data(ujson_t *uj) {
  dif_edn_auto_params_t edn_params =
      edn_testutils_auto_params_build(true, /*res_itval=*/0, /*glen_val=*/0);
  dif_edn_auto_params_t edn_kat_params;
  edn_kat_params.instantiate_cmd.cmd = csrng_cmd_header_build(
      kCsrngAppCmdInstantiate, kDifCsrngEntropySrcToggleDisable,
      kEdnKatSeedMaterialInstantiate.len, /*generate_len=*/0);
  edn_kat_params.instantiate_cmd.seed_material = kEdnKatSeedMaterialInstantiate;
  edn_kat_params.reseed_cmd.cmd = csrng_cmd_header_build(
      kCsrngAppCmdReseed, kDifCsrngEntropySrcToggleDisable,
      kEdnKatSeedMaterialReseed.len,
      /*generate_len=*/0);
  edn_kat_params.reseed_cmd.seed_material = kEdnKatSeedMaterialReseed;
  edn_kat_params.generate_cmd.cmd = csrng_cmd_header_build(
      kCsrngAppCmdGenerate, kDifCsrngEntropySrcToggleDisable,
      kEdnKatSeedMaterialGenerate.len,
      /*generate_len=*/
      kEdnKatOutputLen / kEdnKatWordsPerBlock);

  edn_kat_params.generate_cmd.seed_material = kEdnKatSeedMaterialGenerate;
  edn_kat_params.reseed_interval = 32;

  // Disable the entropy complex.
  TRY(entropy_testutils_stop_all());
  // Enable ENTROPY_SRC in FIPS mode.
  TRY(dif_entropy_src_configure(
      &entropy_src, entropy_testutils_config_default(), kDifToggleEnabled));
  // Enable CSRNG.
  TRY(dif_csrng_configure(&csrng));
  // Enable EDN1 in auto request mode.
  TRY(dif_edn_set_auto_mode(&edn1, edn_params));
  // Enable EDN0 in auto request mode.
  TRY(dif_edn_set_auto_mode(&edn0, edn_kat_params));

  uint32_t ibex_rnd_data[4];

  // Inject faults during generating and receiving random data.
  sca_set_trigger_high();
  asm volatile(NOP10);
  for (size_t it = 0; it < 4; it++) {
    TRY(rv_core_ibex_testutils_get_rnd_data(&rv_core_ibex, kEdnKatTimeout,
                                            &ibex_rnd_data[it]));
  }
  sca_set_trigger_low();

  // Check, if received random data matches the expected data.
  size_t next_val_pos = 0;
  size_t hits = 0;
  size_t it = 0;
  while (it < 4) {
    // If there is a hit, the next potential hit is the current position +1.
    if (ibex_rnd_data[it] == kExpectedOutput[next_val_pos]) {
      next_val_pos = it + 1;
      it++;
      hits++;
    } else {
      // The word has been stolen by another block. Thus, we need to
      // increment the potential next_val_pos.
      next_val_pos = it + 1;
    }
  }
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send result & ERR_STATUS to host.
  edn_fi_test_result_t uj_output;
  uj_output.result = hits;
  uj_output.err_status = codes;
  RESP_OK(ujson_serialize_edn_fi_test_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_edn_fi_init(ujson_t *uj) {
  sca_select_trigger_type(kScaTriggerTypeSw);
  // As we are using the software defined trigger, the first argument of
  // sca_init is not needed. kScaTriggerSourceAes is selected as a placeholder.
  sca_init(kScaTriggerSourceAes, kScaPeripheralIoDiv4 | kScaPeripheralEntropy |
                                     kScaPeripheralCsrng | kScaPeripheralEdn);

  // Disable the instruction cache and dummy instructions for FI attacks.
  sca_configure_cpu();

  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Initialize peripherals used in this FI test.
  TRY(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  TRY(dif_csrng_init(mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR),
                     &csrng));
  TRY(dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));
  TRY(dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn1));

  return OK_STATUS();
}

status_t handle_edn_fi(ujson_t *uj) {
  edn_fi_subcommand_t cmd;
  TRY(ujson_deserialize_edn_fi_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kEdnFiSubcommandInit:
      return handle_edn_fi_init(uj);
    case kEdnFiSubcommandBusData:
      return handle_edn_fi_bus_data(uj);
    case kEdnFiSubcommandBusAck:
      return handle_edn_fi_bus_ack(uj);
    default:
      LOG_ERROR("Unrecognized EDN FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}