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
#include "sw/device/lib/testing/csrng_testutils.h"
#include "sw/device/lib/testing/edn_testutils.h"
#include "sw/device/lib/testing/entropy_src_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/rv_core_ibex_testutils.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/rng_fi_commands.h"

#include "hw/top/edn_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  kEdnKatTimeout = (10 * 1000 * 1000),
  kCsrngExpectedOutputLen = 16,
  kEdnBusAckMaxData = 64,
  kEdnBiasMaxData = 16,
  kEdnKatMaxClen = 12,
  kEdnKatOutputLen = 16,
  kEdnKatWordsPerBlock = 4,
  kEntropyFifoBufferSize = 32,
  kCsrngBiasFWFifoBufferSize = 12,
  kMaxReadCountNotBlocking = 32,
  kTestParamEntropySrcMaxAttempts = 256,
};

static dif_rv_core_ibex_t rv_core_ibex;
static dif_entropy_src_t entropy_src;
static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;
static bool disable_health_check;

static bool firmware_override_init;

static const uint32_t kInputMsg[kCsrngBiasFWFifoBufferSize] = {
    0xa52a0da9, 0xcae141b2, 0x6d5bab9d, 0x2c3e5cc0, 0x225afc93, 0x5d31a610,
    0x91b7f960, 0x0d566bb3, 0xef35e170, 0x94ba7d8e, 0x534eb741, 0x6b60b0da,
};

// Seed material for the EDN KAT instantiate command.
static const dif_edn_seed_material_t kEdnKatSeedMaterialInstantiate = {
    .len = kEdnKatMaxClen,
    .data = {0x73bec010, 0x9262474c, 0x16a30f76, 0x531b51de, 0x2ee494e5,
             0xdfec9db3, 0xcb7a879d, 0x5600419c, 0xca79b0b0, 0xdda33b5c,
             0xa468649e, 0xdf5d73fa},
};
// Seed material for the EDN KAT reseed command.
static const dif_edn_seed_material_t kEdnKatSeedMaterialReseed = {
    .len = kEdnKatMaxClen,
    .data = {0x73bec010, 0x9262474c, 0x16a30f76, 0x531b51de, 0x2ee494e5,
             0xdfec9db3, 0xcb7a879d, 0x5600419c, 0xca79b0b0, 0xdda33b5c,
             0xa468649e, 0xdf5d73fa},
};
// Seed material for the EDN KAT generate command.
static const dif_edn_seed_material_t kEdnKatSeedMaterialGenerate = {
    .len = 0,
};

static dif_edn_auto_params_t kat_auto_params_build(void) {
  return (dif_edn_auto_params_t){
      .instantiate_cmd =
          {
              .cmd = csrng_cmd_header_build(kCsrngAppCmdInstantiate,
                                            kDifCsrngEntropySrcToggleDisable,
                                            kEdnKatSeedMaterialInstantiate.len,
                                            /*generate_len=*/0),
              .seed_material = kEdnKatSeedMaterialInstantiate,
          },
      .reseed_cmd =
          {
              .cmd = csrng_cmd_header_build(kCsrngAppCmdReseed,
                                            kDifCsrngEntropySrcToggleDisable,
                                            kEdnKatSeedMaterialReseed.len,
                                            /*generate_len=*/0),
              .seed_material = kEdnKatSeedMaterialReseed,
          },
      .generate_cmd =
          {
              .cmd = csrng_cmd_header_build(
                  kCsrngAppCmdGenerate, kDifCsrngEntropySrcToggleDisable,
                  kEdnKatSeedMaterialGenerate.len,
                  /*generate_len=*/
                  kEdnKatOutputLen / kEdnKatWordsPerBlock),
              .seed_material = kEdnKatSeedMaterialGenerate,
          },
      .reseed_interval = 32,
  };
}

/**
 * Flushes the data entropy buffer until there is no data available to read.
 *
 * Asserts test error if any of the returned words is equal to zero. Logs the
 * number of entropy words flushed in a single call.
 *
 * @param entropy An entropy source instance.
 */
static void entropy_data_flush(dif_entropy_src_t *entropy_src) {
  uint32_t entropy_bits;
  uint32_t read_count = 0;

  // TODO: Remove this limit. Entropy source should block if there is no entropy
  // available in FW override mode.
  const uint32_t kMaxReadCount = 128;

  while (dif_entropy_src_is_entropy_available(entropy_src) == kDifOk) {
    CHECK_DIF_OK(dif_entropy_src_non_blocking_read(entropy_src, &entropy_bits));
    CHECK(entropy_bits != 0);
    read_count++;
    if (read_count >= kMaxReadCount) {
      break;
    }
  }
}

/**
 * Stops the entropy_src conditioner.
 *
 * @param entropy_src A entropy source handle.
 */
static void entropy_conditioner_stop(const dif_entropy_src_t *entropy_src) {
  uint32_t fail_count = 0;
  dif_result_t op_result;
  do {
    op_result = dif_entropy_src_conditioner_stop(entropy_src);
    if (op_result == kDifIpFifoFull) {
      CHECK(fail_count++ < kTestParamEntropySrcMaxAttempts);
    } else {
      CHECK_DIF_OK(op_result);
    }
  } while (op_result == kDifIpFifoFull);
}

status_t handle_rng_fi_entropy_src_bias(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  TRY(dif_entropy_src_set_enabled(&entropy_src, kDifToggleDisabled));

  // Setup fips grade entropy that can be read by firmware.
  const dif_entropy_src_config_t config = {
      .fips_enable = true,
      .route_to_firmware = true,
      .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
      .health_test_threshold_scope = false, /*default*/
      .health_test_window_size = 0x0200,    /*default*/
      .alert_threshold = 2,                 /*default*/
  };

  // Re-enable entropy src.
  TRY(dif_entropy_src_configure(&entropy_src, config, kDifToggleEnabled));
  // ensure health tests are actually running
  TRY(entropy_src_testutils_wait_for_state(
      &entropy_src, kDifEntropySrcMainFsmStateContHTRunning));

  entropy_data_flush(&entropy_src);

  uint32_t entropy_bits[kMaxReadCountNotBlocking] = {0};

  pentest_set_trigger_high();
  asm volatile(NOP30);
  for (size_t it = 0; it < kMaxReadCountNotBlocking; it++) {
    while (dif_entropy_src_non_blocking_read(&entropy_src, &entropy_bits[it]) !=
           kDifOk)
      ;
  }
  asm volatile(NOP30);
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Send result & ERR_STATUS to host.
  rng_fi_entropy_src_bias_t uj_output;
  // Send result & ERR_STATUS to host.
  memcpy(uj_output.rand, entropy_bits, sizeof(entropy_bits));
  uj_output.err_status = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_rng_fi_entropy_src_bias_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_rng_fi_firmware_override(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  if (!firmware_override_init) {
    // Check if we keep heal tests enabled.
    rng_fi_fw_overwrite_health_t uj_data;
    TRY(ujson_deserialize_rng_fi_fw_overwrite_health_t(uj, &uj_data));
    disable_health_check = uj_data.disable_health_check;

    firmware_override_init = true;
  }

  TRY(entropy_testutils_stop_all());

  if (disable_health_check) {
    // Disable all health tests.
    TRY(entropy_src_testutils_disable_health_tests(&entropy_src));
  }

  TRY(entropy_src_testutils_fw_override_enable(&entropy_src,
                                               kEntropyFifoBufferSize,
                                               /*route_to_firmware=*/true,
                                               /*bypass_conditioner=*/true));

  entropy_data_flush(&entropy_src);

  uint32_t buf[kEntropyFifoBufferSize] = {0};

  pentest_set_trigger_high();
  asm volatile(NOP30);
  for (size_t it = 0; it < kEntropyFifoBufferSize; it++) {
    while (buf[it] == 0) {
      TRY(dif_entropy_src_observe_fifo_blocking_read(&entropy_src, &buf[it],
                                                     kEntropyFifoBufferSize));
    }
  }

  asm volatile(NOP30);
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Send result & ERR_STATUS to host.
  rng_fi_fw_overwrite_t uj_output;
  // Send result & ERR_STATUS to host.
  memcpy(uj_output.rand, buf, sizeof(buf));
  uj_output.err_status = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_rng_fi_fw_overwrite_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_rng_fi_edn_bias(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  TRY(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  TRY(dif_csrng_init(mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR),
                     &csrng));
  TRY(dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));
  TRY(dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn1));
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  dif_edn_auto_params_t edn_params =
      edn_testutils_auto_params_build(true, /*res_itval=*/0, /*glen_val=*/0);
  // Disable the entropy complex.
  TRY(entropy_testutils_stop_all());
  // Enable ENTROPY_SRC in FIPS mode.
  TRY(entropy_testutils_entropy_src_init());
  // Enable CSRNG.
  TRY(dif_csrng_configure(&csrng));
  // Enable EDN1 in auto request mode.
  TRY(dif_edn_set_auto_mode(&edn1, edn_params));
  // Enable EDN0 in auto request mode.
  TRY(dif_edn_set_auto_mode(&edn0, kat_auto_params_build()));

  rng_fi_edn_t uj_output;
  memset(uj_output.rand, 0, sizeof(uj_output.rand));

  pentest_set_trigger_high();
  asm volatile(NOP30);
  for (size_t it = 0; it < kEdnBiasMaxData; it++) {
    CHECK_STATUS_OK(rv_core_ibex_testutils_get_rnd_data(
        &rv_core_ibex, kEdnKatTimeout, &uj_output.rand[it]));
  }
  asm volatile(NOP30);
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Send result & ERR_STATUS to host.
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  uj_output.err_status = err_ibx;
  RESP_OK(ujson_serialize_rng_fi_edn_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_rng_fi_edn_resp_ack(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Enable entropy complex, CSRNG and EDN so Ibex can get entropy.
  // Configure entropy in auto_mode to avoid starving the system from entropy,
  // given that boot mode entropy has a limited number of generated bits.
  TRY(entropy_testutils_auto_mode_init());

  uint32_t ibex_rnd_data[kEdnBusAckMaxData];

  // Inject faults during generating and receiving random data.
  // Goal is to manipulate ACK on bus to trigger that the same
  // data chunk is transmitted multiple times.
  pentest_set_trigger_high();
  asm volatile(NOP30);
  for (size_t it = 0; it < kEdnBusAckMaxData; it++) {
    TRY(rv_core_ibex_testutils_get_rnd_data(&rv_core_ibex, kEdnKatTimeout,
                                            &ibex_rnd_data[it]));
  }
  pentest_set_trigger_low();

  // Check if there are any collisions.
  rng_fi_edn_collisions_t uj_output;
  memset(uj_output.rand, 0, sizeof(uj_output.rand));
  size_t collisions = 0;
  for (size_t outer = 0; outer < kEdnBusAckMaxData; outer++) {
    for (size_t inner = 0; inner < kEdnBusAckMaxData; inner++) {
      if (outer != inner && ibex_rnd_data[outer] == ibex_rnd_data[inner]) {
        if (collisions < 16) {
          uj_output.rand[collisions] = ibex_rnd_data[outer];
        }
        collisions++;
      }
    }
  }

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Send result & ERR_STATUS to host.
  uj_output.collisions = collisions;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  uj_output.err_status = err_ibx;
  RESP_OK(ujson_serialize_rng_fi_edn_collisions_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_rng_fi_edn_init(ujson_t *uj) {
  penetrationtest_cpuctrl_t uj_cpuctrl_data;
  TRY(ujson_deserialize_penetrationtest_cpuctrl_t(uj, &uj_cpuctrl_data));
  penetrationtest_sensor_config_t uj_sensor_data;
  TRY(ujson_deserialize_penetrationtest_sensor_config_t(uj, &uj_sensor_data));
  penetrationtest_alert_config_t uj_alert_data;
  TRY(ujson_deserialize_penetrationtest_alert_config_t(uj, &uj_alert_data));

  pentest_select_trigger_type(kPentestTriggerTypeSw);
  // As we are using the software defined trigger, the first argument of
  // pentest_init is not needed. kPentestTriggerSourceAes is selected as a
  // placeholder.
  pentest_init(kPentestTriggerSourceAes,
               kPentestPeripheralIoDiv4 | kPentestPeripheralEntropy |
                   kPentestPeripheralCsrng | kPentestPeripheralEdn,
               uj_sensor_data.sensor_ctrl_enable,
               uj_sensor_data.sensor_ctrl_en_fatal);

  // Configure the CPU for the pentest.
  penetrationtest_device_info_t uj_output;
  TRY(pentest_configure_cpu(
      uj_cpuctrl_data.enable_icache, &uj_output.icache_en,
      uj_cpuctrl_data.enable_dummy_instr, &uj_output.dummy_instr_en,
      uj_cpuctrl_data.dummy_instr_count, uj_cpuctrl_data.enable_jittery_clock,
      uj_cpuctrl_data.enable_sram_readback, &uj_output.clock_jitter_locked,
      &uj_output.clock_jitter_en, &uj_output.sram_main_readback_locked,
      &uj_output.sram_ret_readback_locked, &uj_output.sram_main_readback_en,
      &uj_output.sram_ret_readback_en, uj_cpuctrl_data.enable_data_ind_timing,
      &uj_output.data_ind_timing_en));

  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Configure the alert handler. Alerts triggered by IP blocks are captured
  // and reported to the test.
  pentest_configure_alert_handler(
      uj_alert_data.alert_classes, uj_alert_data.enable_alerts,
      uj_alert_data.enable_classes, uj_alert_data.accumulation_thresholds,
      uj_alert_data.signals, uj_alert_data.duration_cycles,
      uj_alert_data.ping_timeout);

  // Initialize peripherals used in this FI test.
  TRY(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  TRY(dif_csrng_init(mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR),
                     &csrng));
  TRY(dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));
  TRY(dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn1));

  // Read rom digest.
  TRY(pentest_read_rom_digest(uj_output.rom_digest));

  // Read device ID and return to host.
  TRY(pentest_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_info_t, uj, &uj_output);

  // Read the sensor config.
  TRY(pentest_send_sensor_config(uj));

  // Read the alert config.
  TRY(pentest_send_alert_config(uj));

  // Read different SKU config fields and return to host.
  TRY(pentest_send_sku_config(uj));

  firmware_override_init = false;

  return OK_STATUS();
}

status_t handle_rng_fi_csrng_bias(ujson_t *uj) {
  // Get the test mode.
  crypto_fi_csrng_mode_t uj_data;
  TRY(ujson_deserialize_crypto_fi_csrng_mode_t(uj, &uj_data));
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  TRY(csrng_testutils_cmd_ready_wait(&csrng));
  TRY(dif_csrng_uninstantiate(&csrng));

  const dif_csrng_seed_material_t kEntropyInput = {
      .seed_material = {0x73bec010, 0x9262474c, 0x16a30f76, 0x531b51de,
                        0x2ee494e5, 0xdfec9db3, 0xcb7a879d, 0x5600419c,
                        0xca79b0b0, 0xdda33b5c, 0xa468649e, 0xdf5d73fa},
      .seed_material_len = 12,
  };

  CHECK_DIF_OK(dif_csrng_instantiate(&csrng, kDifCsrngEntropySrcToggleDisable,
                                     &kEntropyInput));

  // FI code target.
  uint32_t rand_data_got[kCsrngExpectedOutputLen];
  TRY(csrng_testutils_cmd_ready_wait(&csrng));

  if (uj_data.all_trigger || uj_data.start_trigger) {
    pentest_set_trigger_high();
  }
  TRY(dif_csrng_generate_start(&csrng, NULL, kCsrngExpectedOutputLen));
  if (uj_data.start_trigger) {
    pentest_set_trigger_low();
  }

  if (uj_data.valid_trigger) {
    pentest_set_trigger_high();
  }
  dif_csrng_output_status_t output_status;
  do {
    TRY(dif_csrng_get_output_status(&csrng, &output_status));
  } while (!output_status.valid_data);
  if (uj_data.valid_trigger) {
    pentest_set_trigger_low();
  }

  if (uj_data.read_trigger) {
    pentest_set_trigger_high();
  }
  TRY(dif_csrng_generate_read(&csrng, rand_data_got, kCsrngExpectedOutputLen));
  if (uj_data.all_trigger || uj_data.read_trigger) {
    pentest_set_trigger_low();
  }

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  // Compare with expected data.
  const uint32_t kExpectedOutput[kCsrngExpectedOutputLen] = {
      932170270,  3480632584, 387346064,  186012424,  899661374,  2795183089,
      336687633,  3222931513, 1490543709, 3319795384, 3464147855, 1850271046,
      1239323641, 2292604615, 3314177342, 1567494162,
  };
  rng_fi_csrng_output_t uj_output;
  uj_output.res = 0;
  for (size_t it = 0; it < kCsrngExpectedOutputLen; it++) {
    if (rand_data_got[it] != kExpectedOutput[it]) {
      uj_output.res = 1;
    }
  }

  // Send result & ERR_STATUS to host.
  memcpy(uj_output.rand, rand_data_got, sizeof(rand_data_got));
  uj_output.err_status = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_rng_fi_csrng_output_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_rng_fi_csrng_bias_fw_override(ujson_t *uj, bool static_seed) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  uint32_t received_data[kCsrngBiasFWFifoBufferSize];
  const dif_csrng_seed_material_t kEmptySeedMaterial = {0};

  uint32_t seed[kCsrngBiasFWFifoBufferSize];

  if (static_seed) {
    memcpy(seed, kInputMsg, sizeof(kInputMsg));
  } else {
    rng_fi_seed_t uj_data;
    TRY(ujson_deserialize_rng_fi_seed_t(uj, &uj_data));
    memcpy(seed, uj_data.seed, sizeof(uj_data.seed));
  }

  CHECK_STATUS_OK(entropy_testutils_stop_all());
  CHECK_STATUS_OK(entropy_src_testutils_fw_override_enable(
      &entropy_src, kCsrngBiasFWFifoBufferSize,
      /*route_to_firmware=*/false,
      /*bypass_conditioner=*/false));

  entropy_data_flush(&entropy_src);

  CHECK_DIF_OK(dif_csrng_configure(&csrng));

  CHECK_DIF_OK(dif_entropy_src_conditioner_start(&entropy_src));

  uint32_t fail_count = 0;
  uint32_t total = 0;
  do {
    uint32_t count;
    dif_result_t op_result = dif_entropy_src_fw_ov_data_write(
        &entropy_src, seed + total, ARRAYSIZE(seed) - total, &count);
    total += count;
    if (op_result == kDifIpFifoFull) {
      CHECK(fail_count++ < kTestParamEntropySrcMaxAttempts);
    } else {
      fail_count = 0;
      CHECK_DIF_OK(op_result);
    }
  } while (total < ARRAYSIZE(seed));

  pentest_set_trigger_high();
  entropy_conditioner_stop(&entropy_src);

  TRY(csrng_testutils_cmd_ready_wait(&csrng));
  CHECK_DIF_OK(dif_csrng_instantiate(&csrng, kDifCsrngEntropySrcToggleEnable,
                                     &kEmptySeedMaterial));

  CHECK_STATUS_OK(csrng_testutils_cmd_generate_run(&csrng, NULL, received_data,
                                                   ARRAYSIZE(received_data)));

  asm volatile(NOP30);
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register from Ibex.
  dif_rv_core_ibex_error_status_t err_ibx;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &err_ibx));

  rng_fi_csrng_ov_output_t uj_output;

  // Send result & ERR_STATUS to host.
  uj_output.res = 0;  // No result is returned.
  memcpy(uj_output.rand, received_data, sizeof(received_data));
  uj_output.err_status = err_ibx;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_rng_fi_csrng_ov_output_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_rng_fi_csrng_init(ujson_t *uj) {
  penetrationtest_cpuctrl_t uj_cpuctrl_data;
  TRY(ujson_deserialize_penetrationtest_cpuctrl_t(uj, &uj_cpuctrl_data));
  penetrationtest_sensor_config_t uj_sensor_data;
  TRY(ujson_deserialize_penetrationtest_sensor_config_t(uj, &uj_sensor_data));
  penetrationtest_alert_config_t uj_alert_data;
  TRY(ujson_deserialize_penetrationtest_alert_config_t(uj, &uj_alert_data));

  pentest_select_trigger_type(kPentestTriggerTypeSw);
  // As we are using the software defined trigger, the first argument of
  // pentest_init is not needed. kPentestTriggerSourceAes is selected as a
  // placeholder.
  pentest_init(kPentestTriggerSourceAes,
               kPentestPeripheralIoDiv4 | kPentestPeripheralCsrng,
               uj_sensor_data.sensor_ctrl_enable,
               uj_sensor_data.sensor_ctrl_en_fatal);

  // Configure the CPU for the pentest.
  penetrationtest_device_info_t uj_output;
  TRY(pentest_configure_cpu(
      uj_cpuctrl_data.enable_icache, &uj_output.icache_en,
      uj_cpuctrl_data.enable_dummy_instr, &uj_output.dummy_instr_en,
      uj_cpuctrl_data.dummy_instr_count, uj_cpuctrl_data.enable_jittery_clock,
      uj_cpuctrl_data.enable_sram_readback, &uj_output.clock_jitter_locked,
      &uj_output.clock_jitter_en, &uj_output.sram_main_readback_locked,
      &uj_output.sram_ret_readback_locked, &uj_output.sram_main_readback_en,
      &uj_output.sram_ret_readback_en, uj_cpuctrl_data.enable_data_ind_timing,
      &uj_output.data_ind_timing_en));

  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Configure the alert handler. Alerts triggered by IP blocks are captured
  // and reported to the test.
  pentest_configure_alert_handler(
      uj_alert_data.alert_classes, uj_alert_data.enable_alerts,
      uj_alert_data.enable_classes, uj_alert_data.accumulation_thresholds,
      uj_alert_data.signals, uj_alert_data.duration_cycles,
      uj_alert_data.ping_timeout);

  // Initialize CSRNG.
  mmio_region_t base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR);
  CHECK_DIF_OK(dif_csrng_init(base_addr, &csrng));
  CHECK_DIF_OK(dif_csrng_configure(&csrng));

  // Read rom digest.
  TRY(pentest_read_rom_digest(uj_output.rom_digest));

  // Read device ID and return to host.
  TRY(pentest_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_info_t, uj, &uj_output);

  // Read the sensor config.
  TRY(pentest_send_sensor_config(uj));

  // Read the alert config.
  TRY(pentest_send_alert_config(uj));

  // Read different SKU config fields and return to host.
  TRY(pentest_send_sku_config(uj));

  return OK_STATUS();
}

status_t handle_rng_fi(ujson_t *uj) {
  rng_fi_subcommand_t cmd;
  TRY(ujson_deserialize_rng_fi_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kRngFiSubcommandCsrngInit:
      return handle_rng_fi_csrng_init(uj);
    case kRngFiSubcommandCsrngBias:
      return handle_rng_fi_csrng_bias(uj);
    case kRngFiSubcommandCsrngBiasFWOverride:
      return handle_rng_fi_csrng_bias_fw_override(uj, false);
    case kRngFiSubcommandCsrngBiasFWOverrideStatic:
      return handle_rng_fi_csrng_bias_fw_override(uj, true);
    case kRngFiSubcommandEdnInit:
      return handle_rng_fi_edn_init(uj);
    case kRngFiSubcommandEdnRespAck:
      return handle_rng_fi_edn_resp_ack(uj);
    case kRngFiSubcommandEdnBias:
      return handle_rng_fi_edn_bias(uj);
    case kRngFiSubcommandFWOverride:
      return handle_rng_fi_firmware_override(uj);
    case kRngFiSubcommandEntropySrcBias:
      return handle_rng_fi_entropy_src_bias(uj);
    default:
      LOG_ERROR("Unrecognized RNG FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
