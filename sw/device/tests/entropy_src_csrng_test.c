// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/csrng_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/otbn_randomness_impl.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;
static dif_entropy_src_t entropy_src;
static dif_otbn_t otbn;
static dif_rv_plic_t plic;

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
  kTestParamNumIterationsOther = 20,
};

/**
 * Interrupt flag IDs. Used to index the interrupt flags used in this test.
 */
typedef enum irq_flag_id {
  kTestIrqFlagIdCsrngEntropyReq,
  kTestIrqFlagIdEdn1CmdDone,
  kTestIrqFlagIdEdn0CmdDone,
  kTestIrqFlagCount,
} irq_flag_id_t;

/**
 * Interrupt flags. Set by `ottf_external_isr()` and cleared by
 * `plic_interrupts_enable()`.
 */
static volatile bool irq_flags[kTestIrqFlagCount];

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
  CHECK_DIF_OK(
      dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));
}

/**
 * Enables the interrupts required by this test.
 */
static void plic_interrupts_enable(void) {
  irq_external_ctrl(false);
  irq_global_ctrl(false);

  for (size_t i = 0; i < kTestIrqFlagCount; ++i) {
    irq_flags[i] = false;
  }

  dif_rv_plic_irq_id_t irq_ids[] = {kTopEarlgreyPlicIrqIdCsrngCsEntropyReq,
                                    kTopEarlgreyPlicIrqIdEdn0EdnCmdReqDone,
                                    kTopEarlgreyPlicIrqIdEdn1EdnCmdReqDone};
  for (size_t i = 0; i < ARRAYSIZE(irq_ids); ++i) {
    CHECK_DIF_OK(
        dif_rv_plic_irq_set_priority(&plic, irq_ids[i], /*priority=*/1u));
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
        &plic, irq_ids[i], kTopEarlgreyPlicTargetIbex0, kDifToggleEnabled));
  }

  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(
      &plic, kTopEarlgreyPlicTargetIbex0, /*threshold=*/0u));

  CHECK_DIF_OK(dif_csrng_irq_set_enabled(&csrng, kDifCsrngIrqCsEntropyReq,
                                         kDifToggleEnabled));
  CHECK_DIF_OK(dif_edn_irq_set_enabled(&edn0, kDifEdnIrqEdnCmdReqDone,
                                       kDifToggleEnabled));
  CHECK_DIF_OK(dif_edn_irq_set_enabled(&edn1, kDifEdnIrqEdnCmdReqDone,
                                       kDifToggleEnabled));

  irq_global_ctrl(true);
  irq_external_ctrl(true);
}

/**
 * Blocks until the interrupt flag with `isr_id` is set to true by the
 * `ottf_external_isr()` routine.
 */
static void irq_block_wait(irq_flag_id_t isr_id) {
  // The interrupt can come before we enter sleep, so we check beforehand.
  while (true) {
    if (irq_flags[isr_id]) {
      break;
    }
    wait_for_interrupt();
  }
  switch (isr_id) {
    case kTestIrqFlagIdCsrngEntropyReq:
      CHECK_DIF_OK(dif_csrng_irq_set_enabled(&csrng, kDifCsrngIrqCsEntropyReq,
                                             kDifToggleDisabled));
      break;
    case kTestIrqFlagIdEdn0CmdDone:
      CHECK_DIF_OK(dif_edn_irq_set_enabled(&edn0, kDifEdnIrqEdnCmdReqDone,
                                           kDifToggleDisabled));
      break;
    case kTestIrqFlagIdEdn1CmdDone:
      CHECK_DIF_OK(dif_edn_irq_set_enabled(&edn0, kDifEdnIrqEdnCmdReqDone,
                                           kDifToggleDisabled));
      break;
    default:
      CHECK(false, "Invalid isr_id: %d", isr_id);
  }
}

/**
 * Requests data from CSRNG software instance.
 *
 * Asserts error if there are any repeated words in the output data, or if there
 * are any errors set in the CSRNG status registers.
 */
static void csrng_generate_output_check(void) {
  uint32_t output[kTestParamFifoBufferSize] = {0};
  CHECK_STATUS_OK(
      csrng_testutils_cmd_generate_run(&csrng, output, ARRAYSIZE(output)));

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
  CHECK_STATUS_OK(entropy_testutils_stop_all());
  CHECK_DIF_OK(dif_entropy_src_configure(
      &entropy_src, entropy_testutils_config_default(), kDifToggleEnabled));
  CHECK_DIF_OK(dif_csrng_configure(&csrng));

  CHECK_STATUS_OK(csrng_testutils_cmd_ready_wait(&csrng));
  plic_interrupts_enable();
  CHECK_DIF_OK(dif_csrng_instantiate(&csrng, kDifCsrngEntropySrcToggleEnable,
                                     seed_material));
  irq_block_wait(kTestIrqFlagIdCsrngEntropyReq);
  csrng_generate_output_check();

  plic_interrupts_enable();
  CHECK_DIF_OK(dif_csrng_reseed(&csrng, seed_material));
  irq_block_wait(kTestIrqFlagIdCsrngEntropyReq);
  csrng_generate_output_check();

  CHECK_STATUS_OK(csrng_testutils_cmd_status_check(&csrng));
  CHECK_STATUS_OK(csrng_testutils_recoverable_alerts_check(&csrng));
}

/**
 * Blocks until EDN is ready to process commands.
 *
 * @param edn A EDN instance.
 */
static void edn_ready_wait(const dif_edn_t *edn) {
  bool ready = false;
  while (!ready) {
    CHECK_DIF_OK(dif_edn_get_status(edn, kDifEdnStatusReady, &ready));
  }
  bool ack_err;
  CHECK_DIF_OK(dif_edn_get_status(edn, kDifEdnStatusCsrngAck, &ack_err));
  CHECK(!ack_err, "Unexpected CSRNG ack error");
}

/**
 * Configures the `edn` instance.
 *
 * Verifies that the entropy req interrupt is triggered on EDN instantiate and
 * reseed commands.
 *
 * @param edn A EDN instance.
 * @param irq_flag_id The interrupt flag ID to poll after each command is sent
 * to EDN.
 * @param seed_material Seed material used in instantiate and reseed commands.
 */
static void edn_configure(const dif_edn_t *edn, irq_flag_id_t irq_flag_id,
                          const dif_edn_seed_material_t *seed_material) {
  CHECK_DIF_OK(dif_edn_configure(edn));

  edn_ready_wait(edn);
  plic_interrupts_enable();
  CHECK_DIF_OK(
      dif_edn_instantiate(edn, kDifEdnEntropySrcToggleEnable, seed_material));
  irq_block_wait(kTestIrqFlagIdCsrngEntropyReq);
  irq_block_wait(irq_flag_id);

  edn_ready_wait(edn);
  plic_interrupts_enable();
  CHECK_DIF_OK(dif_edn_reseed(edn, seed_material));
  irq_block_wait(kTestIrqFlagIdCsrngEntropyReq);
  irq_block_wait(irq_flag_id);

  edn_ready_wait(edn);
}

/**
 * Initializes EDN instances using the `SW_CMD_REQ` interface and runs the OTBN
 * randomness test to verify the entropy delivered by EDN0 and EDN1.
 *
 * @param seed_material Seed material used in EDN instantiate and reseed
 * commands.
 */
static void test_edn_cmd_done(const dif_edn_seed_material_t *seed_material) {
  CHECK_STATUS_OK(entropy_testutils_stop_all());
  CHECK_DIF_OK(dif_entropy_src_configure(
      &entropy_src, entropy_testutils_config_default(), kDifToggleEnabled));
  CHECK_DIF_OK(dif_csrng_configure(&csrng));

  edn_configure(&edn0, kTestIrqFlagIdEdn0CmdDone, seed_material);
  edn_configure(&edn1, kTestIrqFlagIdEdn1CmdDone, seed_material);

  plic_interrupts_enable();

  // Generate enough entropy for the otbn randomness test.
  // The len provided here is in number of words as opposed to num of 128b
  // blocks. The requested len **must** also be equal to the amount of entroy
  // required by the OTBN randomness test, otherwise the Generate command will
  // not be fully executed, causing a hang in the `irq_block_wait()` calls
  // following the end of the OTBN test.
  // EDN0: 20 words = 5x128b blocks
  // EDN1: 44 words = 11x128b blocks
  CHECK_DIF_OK(dif_edn_generate_start(&edn0, /*len=*/1));
  CHECK_DIF_OK(dif_edn_generate_start(&edn1, /*len=*/1));
  edn_ready_wait(&edn0);
  edn_ready_wait(&edn1);
  CHECK_STATUS_OK(
      entropy_testutils_error_check(&entropy_src, &csrng, &edn0, &edn1));

  LOG_INFO("OTBN:START");
  otbn_randomness_test_start(&otbn, /*iters=*/0);

  bool busy = true;
  while (busy) {
    // Clearing `irq_flags` is ok here since there are no other in-flight
    // commands being sent from the EDN instances to the CSRNG block.
    if (irq_flags[kTestIrqFlagIdEdn0CmdDone]) {
      irq_flags[kTestIrqFlagIdEdn0CmdDone] = false;
      CHECK_DIF_OK(dif_edn_generate_start(&edn0, /*len=*/1));
    }
    if (irq_flags[kTestIrqFlagIdEdn1CmdDone]) {
      irq_flags[kTestIrqFlagIdEdn1CmdDone] = false;
      CHECK_DIF_OK(dif_edn_generate_start(&edn1, /*len=*/1));
    }
    // Check if OTBN is still running.
    dif_otbn_status_t status;
    CHECK_DIF_OK(dif_otbn_get_status(&otbn, &status));
    busy = status != kDifOtbnStatusIdle && status != kDifOtbnStatusLocked;
  }

  CHECK(otbn_randomness_test_end(&otbn, /*skip_otbn_done_check=*/false));
  LOG_INFO("OTBN:END");

  // See comment above regarding generate command length and potential test
  // locking issues.
  irq_block_wait(kTestIrqFlagIdEdn1CmdDone);
  irq_block_wait(kTestIrqFlagIdEdn0CmdDone);
  LOG_INFO("DONE");

  plic_interrupts_enable();
  CHECK_DIF_OK(dif_edn_uninstantiate(&edn0));
  irq_block_wait(kTestIrqFlagIdEdn0CmdDone);

  plic_interrupts_enable();
  CHECK_DIF_OK(dif_edn_uninstantiate(&edn1));
  irq_block_wait(kTestIrqFlagIdEdn1CmdDone);

  CHECK_STATUS_OK(csrng_testutils_recoverable_alerts_check(&csrng));
  CHECK_STATUS_OK(
      entropy_testutils_error_check(&entropy_src, &csrng, &edn0, &edn1));
}

void ottf_external_isr(void) {
  // Claim the IRQ at the PLIC.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(&plic, kTopEarlgreyPlicTargetIbex0, &plic_irq_id));

  // Get the peripheral the IRQ belongs to.
  top_earlgrey_plic_peripheral_t peripheral_serviced =
      (top_earlgrey_plic_peripheral_t)
          top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the IRQ that was fired from the PLIC IRQ ID and set the corresponding
  // `irq_flags`.
  if (peripheral_serviced == kTopEarlgreyPlicPeripheralCsrng) {
    dif_csrng_irq_t irq =
        (dif_csrng_irq_t)(plic_irq_id - kTopEarlgreyPlicIrqIdCsrngCsCmdReqDone);
    CHECK(irq == kDifCsrngIrqCsEntropyReq, "Unexpected irq: 0x%x", irq);
    CHECK_DIF_OK(dif_csrng_irq_acknowledge(&csrng, irq));
    irq_flags[kTestIrqFlagIdCsrngEntropyReq] = true;
  } else if (peripheral_serviced == kTopEarlgreyPlicPeripheralEdn0) {
    dif_edn_irq_t irq =
        (dif_edn_irq_t)(plic_irq_id - kTopEarlgreyPlicIrqIdEdn0EdnCmdReqDone);
    CHECK(irq == kDifEdnIrqEdnCmdReqDone, "Unexpected irq: 0x%x", irq);
    CHECK_DIF_OK(dif_edn_irq_acknowledge(&edn0, irq));
    irq_flags[kTestIrqFlagIdEdn0CmdDone] = true;
  } else if (peripheral_serviced == kTopEarlgreyPlicPeripheralEdn1) {
    dif_edn_irq_t irq =
        (dif_edn_irq_t)(plic_irq_id - kTopEarlgreyPlicIrqIdEdn1EdnCmdReqDone);
    CHECK(irq == kDifEdnIrqEdnCmdReqDone, "Unexpected irq: 0x%x", irq);
    CHECK_DIF_OK(dif_edn_irq_acknowledge(&edn1, irq));
    irq_flags[kTestIrqFlagIdEdn1CmdDone] = true;
  }

  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kTopEarlgreyPlicTargetIbex0,
                                        plic_irq_id));
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
    test_edn_cmd_done(&edn_seed);
  }

  return true;
}
