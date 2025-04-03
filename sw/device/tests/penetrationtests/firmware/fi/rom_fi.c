// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/rom_fi.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_rom_ctrl.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/rom_fi_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rom_ctrl_regs.h"

// Interface to Ibex.
static dif_rv_core_ibex_t rv_core_ibex;

static dif_rom_ctrl_t rom_ctrl;

status_t handle_rom_read(ujson_t *uj) {
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  dif_rom_ctrl_digest_t expected_digest;
  dif_rom_ctrl_digest_t fi_digest[8];
  TRY(dif_rom_ctrl_get_digest(&rom_ctrl, &expected_digest));

  pentest_set_trigger_high();
  asm volatile(NOP30);
  TRY(dif_rom_ctrl_get_digest(&rom_ctrl, &fi_digest[0]));
  TRY(dif_rom_ctrl_get_digest(&rom_ctrl, &fi_digest[1]));
  TRY(dif_rom_ctrl_get_digest(&rom_ctrl, &fi_digest[2]));
  TRY(dif_rom_ctrl_get_digest(&rom_ctrl, &fi_digest[3]));
  TRY(dif_rom_ctrl_get_digest(&rom_ctrl, &fi_digest[4]));
  TRY(dif_rom_ctrl_get_digest(&rom_ctrl, &fi_digest[5]));
  TRY(dif_rom_ctrl_get_digest(&rom_ctrl, &fi_digest[6]));
  TRY(dif_rom_ctrl_get_digest(&rom_ctrl, &fi_digest[7]));
  asm volatile(NOP30);
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  rom_fi_digest_t uj_output;
  memset(uj_output.digest, 0, sizeof(uj_output.digest));
  for (size_t i = 0; i < 8; i++) {
    if (memcmp(&expected_digest, &fi_digest[i],
               ROM_CTRL_DIGEST_MULTIREG_COUNT)) {
      uj_output.digest[i] =
          fi_digest[i]
              .digest[0];  // Just return the first 32-bit of the digest.
    }
  }

  // Send the first 8 bytes of the digest and the alerts back to the host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_rom_fi_digest_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_rom_fi_init(ujson_t *uj) {
  penetrationtest_cpuctrl_t uj_data;
  TRY(ujson_deserialize_penetrationtest_cpuctrl_t(uj, &uj_data));

  pentest_select_trigger_type(kPentestTriggerTypeSw);
  pentest_init(kPentestTriggerSourceAes,
               kPentestPeripheralIoDiv4 | kPentestPeripheralEdn |
                   kPentestPeripheralCsrng | kPentestPeripheralEntropy |
                   kPentestPeripheralKmac);

  // Configure the alert handler. Alerts triggered by IP blocks are captured
  // and reported to the test.
  pentest_configure_alert_handler();

  // Configure the CPU for the pentest.
  penetrationtest_device_info_t uj_output;
  TRY(pentest_configure_cpu(
      uj_data.icache_disable, uj_data.dummy_instr_disable,
      uj_data.enable_jittery_clock, uj_data.enable_sram_readback,
      &uj_output.clock_jitter_locked, &uj_output.clock_jitter_en,
      &uj_output.sram_main_readback_locked, &uj_output.sram_ret_readback_locked,
      &uj_output.sram_main_readback_en, &uj_output.sram_ret_readback_en));

  // Initialize rom_ctrl.
  mmio_region_t rom_ctrl_reg =
      mmio_region_from_addr(TOP_EARLGREY_ROM_CTRL_REGS_BASE_ADDR);
  TRY(dif_rom_ctrl_init(rom_ctrl_reg, &rom_ctrl));

  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Read device ID and return to host.
  TRY(pentest_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_info_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_rom_fi(ujson_t *uj) {
  rom_fi_subcommand_t cmd;
  TRY(ujson_deserialize_rom_fi_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kRomFiSubcommandInit:
      return handle_rom_fi_init(uj);
    case kRomFiSubcommandRead:
      return handle_rom_read(uj);
    default:
      LOG_ERROR("Unrecognized Rom FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
