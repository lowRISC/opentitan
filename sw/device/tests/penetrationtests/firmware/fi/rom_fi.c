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
#include "sw/device/sca/lib/sca.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/rom_fi_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rom_ctrl_regs.h"

// NOP macros.
#define NOP1 "addi x0, x0, 0\n"
#define NOP10 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1
#define NOP30 NOP10 NOP10 NOP10

// Interface to Ibex.
static dif_rv_core_ibex_t rv_core_ibex;

static dif_rom_ctrl_t rom_ctrl;

status_t handle_rom_read(ujson_t *uj) {
  sca_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  dif_rom_ctrl_digest_t expected_digest;
  dif_rom_ctrl_digest_t fi_digest[8];
  TRY(dif_rom_ctrl_get_digest(&rom_ctrl, &expected_digest));

  sca_set_trigger_high();
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
  sca_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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
  RESP_OK(ujson_serialize_rom_fi_digest_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_rom_fi_init(ujson_t *uj) {
  sca_select_trigger_type(kScaTriggerTypeSw);
  sca_init(kScaTriggerSourceAes,
           kScaPeripheralIoDiv4 | kScaPeripheralEdn | kScaPeripheralCsrng |
               kScaPeripheralEntropy | kScaPeripheralKmac);

  // Configure the alert handler. Alerts triggered by IP blocks are captured
  // and reported to the test.
  pentest_configure_alert_handler();

  // Disable the instruction cache and dummy instructions for FI attacks.
  pentest_configure_cpu();

  // Initialize rom_ctrl.
  mmio_region_t rom_ctrl_reg =
      mmio_region_from_addr(TOP_EARLGREY_ROM_CTRL_REGS_BASE_ADDR);
  TRY(dif_rom_ctrl_init(rom_ctrl_reg, &rom_ctrl));

  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Read device ID and return to host.
  penetrationtest_device_id_t uj_output;
  TRY(pentest_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_id_t, uj, &uj_output);

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
