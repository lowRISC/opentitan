// Copyright lowRISC contributors (OpenTitan project).
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
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/rv_core_ibex_testutils.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/edn_sca_commands.h"

#include "edn_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// NOP macros.
#define NOP1 "addi x0, x0, 0\n"
#define NOP10 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1
#define NOP30 NOP10 NOP10 NOP10

enum {
  kEdnKatTimeout = (10 * 1000 * 1000),
  kEdnKatMaxClen = 12,
  kEdnKatOutputLen = 16,
  kEdnKatWordsPerBlock = 4,
  /**
   * Max number of traces per batch.
   */
  kNumBatchOpsMax = 128,
};

static dif_rv_core_ibex_t rv_core_ibex;
static dif_entropy_src_t entropy_src;
static dif_csrng_t csrng;
static dif_edn_t edn0;

// Generate random values used by the test by calling the SCA PRNG.
static void generate_random(size_t num_values, uint32_t values[]) {
  for (size_t i = 0; i < num_values; i++) {
    values[i] = prng_rand_uint32();
  }
}

// Configure the EDN with the provided seed material, set the SCA trigger,
// generate and receive random data, and unset the trigger.
static status_t config_run_edn(uint32_t init_seed[12], uint32_t reseed[12]) {
  // Setup seed material.
  // Seed material for the EDN instantiate command.
  dif_edn_seed_material_t kEdnKatSeedMaterialInstantiate = {
      .len = kEdnKatMaxClen,
      .data = {init_seed[0], init_seed[1], init_seed[2], init_seed[3],
               init_seed[4], init_seed[5], init_seed[6], init_seed[7],
               init_seed[8], init_seed[9], init_seed[10], init_seed[11]}};
  // Seed material for the EDN reseed command.
  dif_edn_seed_material_t kEdnKatSeedMaterialReseed = {
      .len = kEdnKatMaxClen,
      .data = {reseed[0], reseed[1], reseed[2], reseed[3], reseed[4], reseed[5],
               reseed[6], reseed[7], reseed[8], reseed[9], reseed[10],
               reseed[11]}};
  // Seed material for the EDN generate command.
  const dif_edn_seed_material_t kEdnKatSeedMaterialGenerate = {
      .len = 0,
  };

  dif_edn_auto_params_t edn_params;
  edn_params.instantiate_cmd.cmd = csrng_cmd_header_build(
      kCsrngAppCmdInstantiate, kDifCsrngEntropySrcToggleDisable,
      kEdnKatSeedMaterialInstantiate.len, /*generate_len=*/0);
  edn_params.instantiate_cmd.seed_material = kEdnKatSeedMaterialInstantiate;
  edn_params.reseed_cmd.cmd = csrng_cmd_header_build(
      kCsrngAppCmdReseed, kDifCsrngEntropySrcToggleDisable,
      kEdnKatSeedMaterialReseed.len,
      /*generate_len=*/0);
  edn_params.reseed_cmd.seed_material = kEdnKatSeedMaterialReseed;
  edn_params.generate_cmd.cmd = csrng_cmd_header_build(
      kCsrngAppCmdGenerate, kDifCsrngEntropySrcToggleDisable,
      kEdnKatSeedMaterialGenerate.len,
      /*generate_len=*/
      kEdnKatOutputLen / kEdnKatWordsPerBlock);

  edn_params.generate_cmd.seed_material = kEdnKatSeedMaterialGenerate;
  edn_params.reseed_interval = 32;

  // Disable the entropy complex.
  TRY(entropy_testutils_stop_all());
  // Enable ENTROPY_SRC in FIPS mode.
  TRY(dif_entropy_src_configure(
      &entropy_src, entropy_testutils_config_default(), kDifToggleEnabled));
  // Enable CSRNG.
  TRY(dif_csrng_configure(&csrng));
  // Enable EDN0 in auto request mode.
  TRY(dif_edn_set_auto_mode(&edn0, edn_params));

  uint32_t ibex_rnd_data;

  // Capture trace during generation and transportation of random data.
  pentest_set_trigger_high();
  asm volatile(NOP30);
  TRY(rv_core_ibex_testutils_get_rnd_data(&rv_core_ibex, kEdnKatTimeout,
                                          &ibex_rnd_data));
  pentest_set_trigger_low();
  asm volatile(NOP30);

  return OK_STATUS();
}

status_t handle_edn_sca_bus_data(ujson_t *uj) {
  // Get seed material.
  edn_sca_seed_t uj_data;
  TRY(ujson_deserialize_edn_sca_seed_t(uj, &uj_data));

  // Configure EDN with provided seed material, set trigger and start generating
  // and fetching data.
  config_run_edn(uj_data.init_seed, uj_data.reseed);

  // Acknowledge test.
  edn_sca_result_t uj_output;
  uj_output.result = 0;
  RESP_OK(ujson_serialize_edn_sca_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_edn_sca_bus_data_batch_fvsr(ujson_t *uj) {
  // Get seed material.
  edn_sca_seed_batch_t uj_data;
  TRY(ujson_deserialize_edn_sca_seed_batch_t(uj, &uj_data));

  bool sample_fixed = true;
  uint32_t last_value = 0;

  uint32_t init_seed[kNumBatchOpsMax][12];
  uint32_t reseed[kNumBatchOpsMax][12];

  for (size_t it = 0; it < uj_data.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(init_seed[it], uj_data.init_seed, 12 * sizeof(uint32_t));
      memcpy(reseed[it], uj_data.reseed, 12 * sizeof(uint32_t));
    } else {
      // Generate random seeds for the EDN configuration.
      generate_random(12, init_seed[it]);
      generate_random(12, reseed[it]);
    }
    sample_fixed = prng_rand_uint32() & 0x1;
  }

  for (size_t it = 0; it < uj_data.num_iterations; it++) {
    // Configure EDN with random seed material, set trigger and start generating
    // and fetching data.
    TRY(config_run_edn(init_seed[it], reseed[it]));
    last_value = reseed[it][11];
  }

  // Acknowledge test, send last reseed value back to host
  // for verification.
  edn_sca_result_t uj_output;
  uj_output.result = last_value;
  RESP_OK(ujson_serialize_edn_sca_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_edn_sca_bus_data_batch_random(ujson_t *uj) {
  // Get number of iterations.
  edn_sca_batch_t uj_data;
  TRY(ujson_deserialize_edn_sca_batch_t(uj, &uj_data));

  uint32_t init_seed[kNumBatchOpsMax][12];
  uint32_t reseed[kNumBatchOpsMax][12];
  for (size_t it = 0; it < uj_data.num_iterations; it++) {
    // Generate random seeds for the EDN configuration.
    generate_random(12, init_seed[it]);
    generate_random(12, reseed[it]);
  }

  for (size_t it = 0; it < uj_data.num_iterations; it++) {
    // Configure EDN with random seed material, set trigger and start generating
    // and fetching data.
    TRY(config_run_edn(init_seed[it], reseed[it]));
  }

  // Acknowledge test, send last random reseed value back to host
  // for verification.
  edn_sca_result_t uj_output;
  uj_output.result = reseed[uj_data.num_iterations - 1][11];
  RESP_OK(ujson_serialize_edn_sca_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_edn_pentest_init(ujson_t *uj) {
  pentest_select_trigger_type(kPentestTriggerTypeSw);
  // As we are using the software defined trigger, the first argument of
  // pentest_init is not needed. kPentestTriggerSourceAes is selected as a
  // placeholder.
  pentest_init(kPentestTriggerSourceAes,
               kPentestPeripheralIoDiv4 | kPentestPeripheralEntropy |
                   kPentestPeripheralCsrng | kPentestPeripheralEdn);

  // Disable the instruction cache and dummy instructions for SCA attacks.
  pentest_configure_cpu();

  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Initialize peripherals used in this SCA test.
  TRY(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  TRY(dif_csrng_init(mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR),
                     &csrng));
  TRY(dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));

  return OK_STATUS();
}

status_t handle_edn_sca(ujson_t *uj) {
  edn_sca_subcommand_t cmd;
  TRY(ujson_deserialize_edn_sca_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kEdnScaSubcommandBusData:
      return handle_edn_sca_bus_data(uj);
    case kEdnScaSubcommandBusDataBatchFvsr:
      return handle_edn_sca_bus_data_batch_fvsr(uj);
    case kEdnScaSubcommandBusDataBatchRandom:
      return handle_edn_sca_bus_data_batch_random(uj);
    case kEdnScaSubcommandInit:
      return handle_edn_pentest_init(uj);
    default:
      LOG_ERROR("Unrecognized EDN SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
