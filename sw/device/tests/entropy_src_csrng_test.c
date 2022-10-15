// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/csrng_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;
static dif_entropy_src_t entropy_src;
static dif_rv_plic_t plic;

// Set by `ottf_external_isr()` and cleared by
// `csrng_entropy_req_irq_enable()`.
static volatile bool entropy_src_isr_csrng_req_set;

OTTF_DEFINE_TEST_CONFIG();

enum {
  /**
   * The size of the buffer used in firmware to process the entropy bits in
   * firmware override mode.
   */
  kTestParamFifoBufferSize = 12,
  /**
   * The number of test iterations per target.
   */
  kTestParamNumIterationsSim = 1,
  kTestParamNumIterationsOther = 100,
};

/**
 * Initializes the peripherals used in this test.
 */
static void init_peripherals(void) {
  CHECK_DIF_OK(dif_csrng_init(
      mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn1));
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));
}

/**
 * Enables the CSRNG entropy request interrupt.
 */
static void csrng_entropy_req_irq_enable(void) {
  irq_external_ctrl(false);
  irq_global_ctrl(false);

  entropy_src_isr_csrng_req_set = false;

  dif_rv_plic_irq_id_t irq_id = kTopEarlgreyPlicIrqIdCsrngCsEntropyReq;
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(&plic, irq_id, /*priority=*/1u));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      &plic, irq_id, kTopEarlgreyPlicTargetIbex0, kDifToggleEnabled));
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(
      &plic, kTopEarlgreyPlicTargetIbex0, /*threshold=*/0u));

  CHECK_DIF_OK(dif_csrng_irq_set_enabled(&csrng, kDifCsrngIrqCsEntropyReq,
                                         kDifToggleEnabled));

  irq_global_ctrl(true);
  irq_external_ctrl(true);
}

/**
 * Blocks until a CSRNG entropy request interrupt is received.
 */
static void csrng_entropy_req_irq_block_wait(void) {
  // The interrupt can come before we enter sleep, so we check beforehand.
  while (true) {
    if (entropy_src_isr_csrng_req_set) {
      break;
    }
    wait_for_interrupt();
  }
  CHECK_DIF_OK(dif_csrng_irq_set_enabled(&csrng, kDifCsrngIrqCsEntropyReq,
                                         kDifToggleDisabled));
}

/**
 * Requests data from CSRNG software instance.
 *
 * Asserts error if there are any repeated words in the output data, or if there
 * are any errors set in the CSRNG status registers.
 */
static void csrng_generate_output_check(void) {
  uint32_t output[kTestParamFifoBufferSize] = {0};
  csrng_testutils_cmd_generate_run(&csrng, output, ARRAYSIZE(output));

  uint32_t prev_data = 0;
  for (size_t i = 0; i < ARRAYSIZE(output); ++i) {
    CHECK(prev_data != output[i],
          "Received duplicate data. Last index: %d, value: 0x%x", i, prev_data);
  }
}

/**
 * Verifies that the entropy req interrupt is triggered on CSRNG instantiate and
 * reseed commands.
 */
static void test_csrng_sw_entropy_req_interrupt(
    const dif_csrng_seed_material_t *seed_material) {
  entropy_testutils_stop_all();
  CHECK_DIF_OK(dif_entropy_src_configure(
      &entropy_src, entropy_testutils_config_default(), kDifToggleEnabled));
  CHECK_DIF_OK(dif_csrng_configure(&csrng));

  csrng_testutils_cmd_ready_wait(&csrng);
  csrng_entropy_req_irq_enable();
  CHECK_DIF_OK(dif_csrng_instantiate(&csrng, kDifCsrngEntropySrcToggleEnable,
                                     seed_material));
  csrng_entropy_req_irq_block_wait();
  csrng_generate_output_check();

  csrng_entropy_req_irq_enable();
  CHECK_DIF_OK(dif_csrng_reseed(&csrng, seed_material));
  csrng_entropy_req_irq_block_wait();
  csrng_generate_output_check();

  csrng_testutils_cmd_status_check(&csrng);
  csrng_testutils_recoverable_alerts_check(&csrng);
}

/**
 * Verifies that the entropy req interrupt is triggered on EDN instantiate and
 * reseed commands.
 */
static void test_csrng_edn_entropy_req_interrupt(
    const dif_edn_seed_material_t *seed_material) {
  entropy_testutils_stop_all();
  CHECK_DIF_OK(dif_entropy_src_configure(
      &entropy_src, entropy_testutils_config_default(), kDifToggleEnabled));
  CHECK_DIF_OK(dif_csrng_configure(&csrng));

  CHECK_DIF_OK(dif_edn_configure(&edn0));
  csrng_entropy_req_irq_enable();
  CHECK_DIF_OK(
      dif_edn_instantiate(&edn0, kDifEdnEntropySrcToggleEnable, seed_material));
  csrng_entropy_req_irq_block_wait();

  csrng_entropy_req_irq_enable();
  CHECK_DIF_OK(dif_edn_reseed(&edn0, seed_material));
  csrng_entropy_req_irq_block_wait();
  CHECK_DIF_OK(dif_edn_uninstantiate(&edn0));

  CHECK_DIF_OK(dif_edn_configure(&edn1));
  csrng_entropy_req_irq_enable();
  CHECK_DIF_OK(
      dif_edn_instantiate(&edn1, kDifEdnEntropySrcToggleEnable, seed_material));
  csrng_entropy_req_irq_block_wait();

  csrng_entropy_req_irq_enable();
  CHECK_DIF_OK(dif_edn_reseed(&edn1, seed_material));
  csrng_entropy_req_irq_block_wait();
  CHECK_DIF_OK(dif_edn_uninstantiate(&edn1));

  csrng_testutils_recoverable_alerts_check(&csrng);
}

void ottf_external_isr(void) {
  top_earlgrey_plic_peripheral_t plic_peripheral;
  dif_csrng_irq_t irq;
  isr_testutils_csrng_isr(
      (plic_isr_ctx_t){
          .rv_plic = &plic,
          .hart_id = kTopEarlgreyPlicTargetIbex0,
      },
      (csrng_isr_ctx_t){
          .csrng = &csrng,
          .plic_csrng_start_irq_id = kTopEarlgreyPlicIrqIdCsrngCsCmdReqDone,
          .expected_irq = kDifCsrngIrqCsEntropyReq,
          .is_only_irq = false,
      },
      &plic_peripheral, &irq);
  CHECK(plic_peripheral == kTopEarlgreyPlicPeripheralCsrng,
        "Interrupt from incorrect peripheral: (expected: %d, got: %d)",
        kTopEarlgreyPlicPeripheralCsrng, plic_peripheral);
  CHECK(irq == kDifCsrngIrqCsEntropyReq);
  entropy_src_isr_csrng_req_set = true;
}

bool test_main(void) {
  init_peripherals();

  // Get test random parameters before we disable the entropy complex.
  // rand_testutils relies on the ibex rnd CSR which is connected to EDN0.
  dif_csrng_seed_material_t csrng_seed;
  csrng_seed.seed_material_len =
      rand_testutils_gen32_range(/*min=*/0, kDifCsrngSeedMaterialMaxWordLen);
  for (size_t i = 0; i < csrng_seed.seed_material_len; ++i) {
    csrng_seed.seed_material[i] = rand_testutils_gen32();
  }

  dif_edn_seed_material_t edn_seed;
  edn_seed.len =
      rand_testutils_gen32_range(/*min=*/0, kDifEntropySeedMaterialMaxWordLen);
  for (size_t i = 0; i < edn_seed.len; ++i) {
    edn_seed.data[i] = rand_testutils_gen32();
  }

  uint32_t num_iterations = kTestParamNumIterationsSim;
  if (kDeviceType != kDeviceSimDV && kDeviceType != kDeviceSimVerilator) {
    num_iterations = kTestParamNumIterationsOther;
  }

  for (size_t i = 0; i < num_iterations; ++i) {
    test_csrng_sw_entropy_req_interrupt(&csrng_seed);
    test_csrng_edn_entropy_req_interrupt(&edn_seed);
  }

  return true;
}
