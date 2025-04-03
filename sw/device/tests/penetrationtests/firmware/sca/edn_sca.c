// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rv_core_ibex_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/edn_sca_commands.h"

#include "edn_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rv_core_ibex_regs.h"  // Generated

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

/**
 * Read randomness.
 *
 * The goal of this function is to allow the SCA setup to measure randomness
 * transmitted from the 128-bit FIFO within the EDN to the Ibex RND_DATA
 * register.
 *
 * To do so, this function first clears the 128-bit FIFO by reading it. When the
 * FIFO is empty, the EDN sends a request to the CSRNG. When the FIFO again is
 * full, set the SCA trigger and read the randomness from the FIFO to the
 * RND_DATA register.
 *
 * @param ibex_rnd_data The array containing the randomness.
 * @return OK or error.
 */
static status_t read_rnd_data_reg(uint32_t ibex_rnd_data[4]) {
  // Clear the CSRNG FIFO containing randomness before starting the test.
  for (size_t it = 0; it < 4; it++) {
    TRY(dif_rv_core_ibex_read_rnd_data(&rv_core_ibex, &ibex_rnd_data[0]));
  }
  memset(ibex_rnd_data, 0, 4 * sizeof(uint32_t));
  // Wait until RND_DATA_VALID becomes true, i.e., randomness is available.
  bool rnd_data_valid = rv_core_ibex_testutils_is_rnd_data_valid(&rv_core_ibex);
  while (!rnd_data_valid) {
    rnd_data_valid = rv_core_ibex_testutils_is_rnd_data_valid(&rv_core_ibex);
  }

  // Read RND_DATA register. First access contains randomness that already was
  // transmitted over the bus. Afterwards, data needs to be transmitted from the
  // randomness FIFO into the RND_DATA register - this is what we want to
  // measure.
  pentest_set_trigger_high();
  asm volatile(NOP30);
  asm volatile("li t0, %0"
               :
               : "i"(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR)
               : "t0");
  asm volatile("lw t1, %0(t0)"
               :
               : "i"(RV_CORE_IBEX_RND_DATA_REG_OFFSET)
               : "t1");
  asm volatile(NOP30);
  asm volatile(NOP30);
  pentest_set_trigger_low();
  // Read RND_DATA which was transmitted from FIFO into RND_DATA register.
  // Read it after the trigger window to not measure load into Ibex register
  TRY(dif_rv_core_ibex_read_rnd_data(&rv_core_ibex, &ibex_rnd_data[3]));

  return OK_STATUS();
}

status_t handle_edn_sca_bus_data_batch(ujson_t *uj) {
  // Get number of iterations.
  edn_sca_batch_t uj_data;
  uint32_t max_iterations = 128;
  TRY(ujson_deserialize_edn_sca_batch_t(uj, &uj_data));
  CHECK(uj_data.num_iterations <= max_iterations);

  // Start num_iterations trigger windows.
  uint32_t rand_data[max_iterations][4];
  for (size_t it = 0; it < uj_data.num_iterations; it++) {
    TRY(read_rnd_data_reg(rand_data[it]));
  }

  // Send back num_iterations rand_data.
  for (size_t it = 0; it < uj_data.num_iterations; it++) {
    edn_sca_result_t uj_output;
    memcpy(&uj_output.rnd_data, rand_data[it], 4 * sizeof(uint32_t));
    RESP_OK(ujson_serialize_edn_sca_result_t, uj, &uj_output);
  }

  return OK_STATUS();
}

status_t handle_edn_sca_bus_data(ujson_t *uj) {
  edn_sca_result_t uj_output;

  TRY(read_rnd_data_reg(uj_output.rnd_data));

  // Send data back to host.
  RESP_OK(ujson_serialize_edn_sca_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_edn_sca_init(ujson_t *uj) {
  penetrationtest_cpuctrl_t uj_data;
  TRY(ujson_deserialize_penetrationtest_cpuctrl_t(uj, &uj_data));

  pentest_select_trigger_type(kPentestTriggerTypeSw);
  // As we are using the software defined trigger, the first argument of
  // sca_init is not needed. kPentestTriggerSourceAes is selected as a
  // placeholder.
  pentest_init(kPentestTriggerSourceAes,
               kPentestPeripheralIoDiv4 | kPentestPeripheralEntropy |
                   kPentestPeripheralCsrng | kPentestPeripheralEdn);

  // Disable the instruction cache and dummy instructions for SCA attacks.
  penetrationtest_device_info_t uj_output;
  TRY(pentest_configure_cpu(
      uj_data.icache_disable, uj_data.dummy_instr_disable,
      uj_data.enable_jittery_clock, uj_data.enable_sram_readback,
      &uj_output.clock_jitter_locked, &uj_output.clock_jitter_en,
      &uj_output.sram_main_readback_locked, &uj_output.sram_ret_readback_locked,
      &uj_output.sram_main_readback_en, &uj_output.sram_ret_readback_en));

  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Configure the entropy complex. Set the reseed interval to max to avoid
  // reseed during the trigger window.
  TRY(pentest_configure_entropy_source_max_reseed_interval());

  // Read device ID and return to host.
  TRY(pentest_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_info_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_edn_sca(ujson_t *uj) {
  edn_sca_subcommand_t cmd;
  TRY(ujson_deserialize_edn_sca_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kEdnScaSubcommandInit:
      return handle_edn_sca_init(uj);
    case kEdnScaSubcommandBusData:
      return handle_edn_sca_bus_data(uj);
    case kEdnScaSubcommandBusDataBatch:
      return handle_edn_sca_bus_data_batch(uj);
    default:
      LOG_ERROR("Unrecognized EDN SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
