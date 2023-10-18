// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/csrng_testutils.h"
#include "sw/device/lib/testing/edn_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_macros.h"
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
static dif_rv_core_ibex_t rv_core_ibex;

enum {
  /**
   * The number of test iterations per target.
   */
  kTestParamNumIterationsSim = 2,
  kTestParamNumIterationsOther = 20,
  /**
   * The number of test iterations per entropy consumer.
   */
  kTestParamNumOtbnIterationsMax = 4,
  kTestParamNumIbexIterationsMax = 16,
};

/**
 * Test execution states. These are use to control the execution state of all
 * test tasks.
 */
typedef enum test_state {
  /**
   * Configure entropy complex for next test iteration.
   */
  kTestStateSetup,
  /**
   * Request entropy from various endpoints.
   */
  kTestStateRun,
  /**
   * Tear down tasks.
   */
  kTestStateTearDown,
  /**
   * Number of test states.
   */
  kTestStateCount,
} test_state_t;
static volatile test_state_t execution_state;

static const char *kStatusNames[kTestStateCount] = {"Setup", "Run", "TearDown"};
static_assert(ARRAYSIZE(kStatusNames) == kTestStateCount,
              "Unexpected kStatusNames array size.");

/**
 * Each task uses the task ID to update flag and counter arrays.
 */
typedef enum task_id {
  /**
   * Assigned to `main_task()`.
   */
  kTestTaskIdMain,
  /**
   * Assigned to `otbn_task()`.
   */
  kTestTaskIdOtbn,
  /**
   * Assigned to `ibex_task()`.
   */
  kTestTaskIdIbex,
  /**
   * Number of tasks. Used to define task flag and counter arrays.
   */
  kTestTaskIdCount
} task_id_t;
/**
 * Flags used to track when a task is done executing a test iteration.
 */
static volatile bool task_done[kTestTaskIdCount];
/**
 * Flags used to track the number of test iterations per task.
 */
static volatile uint32_t task_iter_count_max[kTestTaskIdCount];

OTTF_DEFINE_TEST_CONFIG(.enable_concurrency = true);

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
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));
  CHECK_DIF_OK(
      dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));
}

/**
 * Helper function used to set the task done flag.
 *
 * Issues a `ottf_task_yield()` to ensure control is handed over to pending
 * tasks.
 *
 * @param task_id The task ID.
 */
static void task_done_set_and_yield(task_id_t task_id) {
  task_done[task_id] = true;
  ottf_task_yield();
}

/**
 * OTBN task.
 *
 * Executes OTBN randomness test, the test state is set to `kTestStateRun`.
 *
 * @param task_parameters Unused. Set to NULL by ottf.
 */
static void otbn_task(void *task_parameters) {
  while (true) {
    if (execution_state == kTestStateTearDown) {
      break;
    }
    if (execution_state == kTestStateSetup || task_done[kTestTaskIdOtbn]) {
      ottf_task_yield();
      continue;
    }
    LOG_INFO("OTBN:START");
    for (size_t i = 0; i < task_iter_count_max[kTestTaskIdOtbn]; ++i) {
      otbn_randomness_test_start(&otbn);
      dif_otbn_status_t status;
      do {
        CHECK_DIF_OK(dif_otbn_get_status(&otbn, &status));
        ottf_task_yield();
      } while (status != kDifOtbnStatusIdle && status != kDifOtbnStatusLocked);
      CHECK(otbn_randomness_test_end(&otbn, /*skip_otbn_done_check=*/false));
    }
    LOG_INFO("OTBN:DONE");
    task_done_set_and_yield(kTestTaskIdOtbn);
  }
  OTTF_TASK_DELETE_SELF_OR_DIE;
}

/**
 * Ibex task.
 *
 * Executes Ibex randomness test the, test state is set to `kTestStateRun`.
 *
 * @param task_parameters Unused. Set to NULL by ottf.
 */
static void ibex_task(void *task_parameters) {
  while (true) {
    if (execution_state == kTestStateTearDown) {
      break;
    }
    if (execution_state == kTestStateSetup || task_done[kTestTaskIdIbex]) {
      ottf_task_yield();
      continue;
    }
    LOG_INFO("Ibex:START");
    uint32_t prev_data = 0;
    for (size_t i = 0; i < task_iter_count_max[kTestTaskIdIbex];) {
      dif_rv_core_ibex_rnd_status_t status;
      CHECK_DIF_OK(dif_rv_core_ibex_get_rnd_status(&rv_core_ibex, &status));
      if ((status & kDifRvCoreIbexRndStatusValid) == 0) {
        ottf_task_yield();
        continue;
      }
      i++;
      uint32_t new_data;
      CHECK_DIF_OK(dif_rv_core_ibex_read_rnd_data(&rv_core_ibex, &new_data));

      // The following checks have a probability of returning false negatives.
      // Flakiness issues can potentially be addressed by switching to error
      // counters.
      CHECK(new_data != prev_data, "Unexpected duplicate data");
      CHECK(new_data != 0);
      CHECK(new_data != UINT32_MAX);
      prev_data = new_data;
    }
    LOG_INFO("Ibex:DONE");
    task_done_set_and_yield(kTestTaskIdIbex);
  }
  OTTF_TASK_DELETE_SELF_OR_DIE;
}

/**
 * Verifies that the entropy req interrupt is triggered on EDN instantiate and
 * reseed commands.
 */
static void entropy_config(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  LOG_INFO("Generating EDN params");
  dif_edn_auto_params_t edn_params0 = edn_testutils_auto_params_build();
  dif_edn_auto_params_t edn_params1 = edn_testutils_auto_params_build();

  task_iter_count_max[kTestTaskIdOtbn] =
      rand_testutils_gen32_range(/*min=*/1, kTestParamNumOtbnIterationsMax);
  task_iter_count_max[kTestTaskIdIbex] =
      rand_testutils_gen32_range(/*min=*/1, kTestParamNumIbexIterationsMax);

  CHECK_STATUS_OK(entropy_testutils_stop_all());
  CHECK_DIF_OK(dif_entropy_src_configure(
      &entropy_src, entropy_testutils_config_default(), kDifToggleEnabled));
  CHECK_DIF_OK(dif_csrng_configure(&csrng));
  CHECK_DIF_OK(dif_edn_set_auto_mode(&edn0, edn_params0));
  CHECK_DIF_OK(dif_edn_set_auto_mode(&edn1, edn_params1));
}

/**
 * Updates and logs the execution state.
 *
 * @param next_state The next state.
 */
static void execution_state_update(test_state_t next_state) {
  CHECK(next_state < kTestStateCount);
  LOG_INFO("Test state: %s", kStatusNames[next_state]);
  execution_state = next_state;
}

/**
 * Main test task.
 *
 * Configures entropy complex and signals test tasks to run an iteration loop.
 *
 * @param task_parameters Unused. Set to NULL by ottf.
 */
static void main_task(void *task_parameters) {
  task_iter_count_max[kTestTaskIdMain] = kTestParamNumIterationsSim;
  if (kDeviceType != kDeviceSimDV && kDeviceType != kDeviceSimVerilator) {
    task_iter_count_max[kTestTaskIdMain] = kTestParamNumIterationsOther;
  }

  uint32_t iter_count = 0;
  while (true) {
    if (execution_state == kTestStateRun) {
      uint32_t count = 0;
      for (size_t i = 0; i < kTestTaskIdCount; ++i) {
        count += task_done[i] ? 1 : 0;
      }
      if (count < kTestTaskIdCount) {
        ottf_task_yield();
        continue;
      }
      // Consider this test iteration done if all tasks are done. Update the
      // iteration counter and set the execution state to `kTestStateSetup`
      // to continue with configuring the entropy blocks for the next test
      // run iteration.
      if (++iter_count >= task_iter_count_max[kTestTaskIdMain]) {
        execution_state_update(kTestStateTearDown);
        break;
      }
      CHECK_STATUS_OK((csrng_testutils_recoverable_alerts_check(&csrng)));
      CHECK_STATUS_OK(
          entropy_testutils_error_check(&entropy_src, &csrng, &edn0, &edn1));
      execution_state_update(kTestStateSetup);
    }
    // The rest of this code block is executed when
    // `execute_state == kTestStateSetup`.
    entropy_config();
    for (size_t i = 0; i < kTestTaskIdCount; ++i) {
      task_done[i] = false;
    }
    // Signal the other tasks to start test execution.
    execution_state_update(kTestStateRun);
    // This is required to ensure the aggregation of task_done entries is equal
    // to `kTestTaskIdCount`.
    task_done_set_and_yield(kTestTaskIdMain);
  }
  OTTF_TASK_DELETE_SELF_OR_DIE;
}

bool test_main(void) {
  init_peripherals();

  // Initialize the test `execution_state` before launching the tasks.
  execution_state_update(kTestStateSetup);

  CHECK(ottf_task_create(main_task, "main", kOttfFreeRtosMinStackSize, 1));
  CHECK(ottf_task_create(otbn_task, "otbn", kOttfFreeRtosMinStackSize, 1));
  CHECK(ottf_task_create(ibex_task, "ibex", kOttfFreeRtosMinStackSize, 1));

  // There is no need to poll for completion as the tasks above will execute
  // with higher priority and control will not be returned to this task until
  // all tasks are done executing.
  ottf_task_yield();
  return true;
}
