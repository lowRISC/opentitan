// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/boot_fi.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_rom_ctrl.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_next_boot_bl0_slot.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/epmp_state.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_manifest.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/boot_fi_commands.h"

#include "hw/top/flash_ctrl_regs.h"
#include "hw/top/rom_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Interface to Ibex.
static dif_rv_core_ibex_t rv_core_ibex;

static manifest_t *get_rom_ext_manifest_a(void) {
  return (manifest_t *)TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR;
}

static manifest_t *get_rom_ext_manifest_b(void) {
  return (manifest_t *)(TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR +
                        (TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES / 2));
}

static manifest_t *get_firmware_manifest_a(void) {
  return (manifest_t *)(TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR +
                        CHIP_ROM_EXT_SIZE_MAX);
}

static manifest_t *get_firmware_manifest_b(void) {
  return (manifest_t *)(TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR +
                        CHIP_ROM_EXT_SIZE_MAX +
                        (TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES / 2));
}

status_t handle_inactive_firmware_invalidation(ujson_t *uj) {
  manifest_t *manifest;

  boot_log_t boot_log = retention_sram_get()->creator.boot_log;

  boot_fi_status_t uj_output;
  uj_output.status = true;

  // Get the inactive manifest.
  if (boot_log.bl0_slot == kBootSlotA) {
    manifest = get_firmware_manifest_b();
  } else {
    manifest = get_firmware_manifest_a();
  }

  flash_ctrl_data_default_perms_set(
      (flash_ctrl_perms_t){.read = kMultiBitBool4True,
                           .write = kMultiBitBool4True,
                           .erase = kMultiBitBool4False});

  uint32_t sig_offset = (uint32_t)&manifest->ecdsa_signature.r[0] -
                        TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR;

  uint32_t zero_val = 0;
  rom_error_t err = flash_ctrl_data_write(sig_offset, 1, &zero_val);

  if (err != kErrorOk) {
    LOG_ERROR("Failed to corrupt ECDSA signature: 0x%08x", err);
    uj_output.status = false;
  }

  const manifest_ext_spx_signature_t *spx_ext;
  err = manifest_ext_get_spx_signature(manifest, &spx_ext);

  if (err == kErrorOk && spx_ext != NULL) {
    uint32_t spx_offset =
        (uint32_t)&spx_ext->signature - TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR;

    err = flash_ctrl_data_write(spx_offset, 1, &zero_val);

    if (err != kErrorOk) {
      LOG_ERROR("Failed to corrupt SPX signature: 0x%08x", err);
      uj_output.status = false;
    }
  }

  RESP_OK(ujson_serialize_boot_fi_status_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_next_boot_slot(ujson_t *uj) {
  retention_sram_t *ret_sram = retention_sram_get();

  boot_log_t boot_log = retention_sram_get()->creator.boot_log;
  uint32_t target_slot =
      (boot_log.primary_bl0_slot == kBootSlotA) ? kBootSlotB : kBootSlotA;

  boot_svc_msg_t msg = {0};

  boot_svc_next_boot_bl0_slot_req_init(
      /*primary_slot=*/target_slot,
      /*next_slot=*/kBootSlotUnspecified, &msg.next_boot_bl0_slot_req);

  ret_sram->creator.boot_svc_msg = msg;

  LOG_INFO("Boot services executed. Next boot will prioritize slot %c.",
           (target_slot == kBootSlotA) ? 'A' : 'B');

  // Reset to get the boot service to take effect.
  rstmgr_reset();
  return OK_STATUS();
}

status_t handle_boot_status(ujson_t *uj) {
  LOG_INFO("===================================");
  LOG_INFO("Component | Status  | Version      ");
  LOG_INFO("-----------------------------------");

  // ROM_EXT A
  if (get_rom_ext_manifest_a()->identifier == CHIP_ROM_EXT_IDENTIFIER) {
    LOG_INFO("ROM_EXT A | Present | %u.%u",
             get_rom_ext_manifest_a()->version_major,
             get_rom_ext_manifest_a()->version_minor);
  } else {
    LOG_ERROR("ROM_EXT A | Missing | N/A");
  }

  // ROM_EXT B
  if (get_rom_ext_manifest_b()->identifier == CHIP_ROM_EXT_IDENTIFIER) {
    LOG_INFO("ROM_EXT B | Present | %u.%u",
             get_rom_ext_manifest_b()->version_major,
             get_rom_ext_manifest_b()->version_minor);
  } else {
    LOG_ERROR("ROM_EXT B | Missing | N/A");
  }

  // BL0 A
  if (get_firmware_manifest_a()->identifier == CHIP_BL0_IDENTIFIER) {
    LOG_INFO("BL0 A     | Present | N/A");
  } else {
    LOG_ERROR("BL0 A     | Missing | N/A");
  }

  // BL0 B
  if (get_firmware_manifest_b()->identifier == CHIP_BL0_IDENTIFIER) {
    LOG_INFO("BL0 B     | Present | N/A");
  } else {
    LOG_ERROR("BL0 B     | Missing | N/A");
  }

  LOG_INFO("===================================");

  boot_log_t boot_log = retention_sram_get()->creator.boot_log;
  LOG_INFO("Booting from ROM_EXT slot %s and BL0 slot %s",
           boot_log.rom_ext_slot == kBootSlotA ? "A" : "B",
           boot_log.bl0_slot == kBootSlotA ? "A" : "B");
  LOG_INFO("Primary slot for BL0 is %s",
           boot_log.primary_bl0_slot == kBootSlotA ? "A" : "B");

  return OK_STATUS();
}

status_t handle_epmp_status(ujson_t *uj) {
  uint32_t pmpcfg[4];
  CSR_READ(CSR_REG_PMPCFG0, &pmpcfg[0]);
  CSR_READ(CSR_REG_PMPCFG1, &pmpcfg[1]);
  CSR_READ(CSR_REG_PMPCFG2, &pmpcfg[2]);
  CSR_READ(CSR_REG_PMPCFG3, &pmpcfg[3]);

  uint32_t pmpaddr[16];
  CSR_READ(CSR_REG_PMPADDR0, &pmpaddr[0]);
  CSR_READ(CSR_REG_PMPADDR1, &pmpaddr[1]);
  CSR_READ(CSR_REG_PMPADDR2, &pmpaddr[2]);
  CSR_READ(CSR_REG_PMPADDR3, &pmpaddr[3]);
  CSR_READ(CSR_REG_PMPADDR4, &pmpaddr[4]);
  CSR_READ(CSR_REG_PMPADDR5, &pmpaddr[5]);
  CSR_READ(CSR_REG_PMPADDR6, &pmpaddr[6]);
  CSR_READ(CSR_REG_PMPADDR7, &pmpaddr[7]);
  CSR_READ(CSR_REG_PMPADDR8, &pmpaddr[8]);
  CSR_READ(CSR_REG_PMPADDR9, &pmpaddr[9]);
  CSR_READ(CSR_REG_PMPADDR10, &pmpaddr[10]);
  CSR_READ(CSR_REG_PMPADDR11, &pmpaddr[11]);
  CSR_READ(CSR_REG_PMPADDR12, &pmpaddr[12]);
  CSR_READ(CSR_REG_PMPADDR13, &pmpaddr[13]);
  CSR_READ(CSR_REG_PMPADDR14, &pmpaddr[14]);
  CSR_READ(CSR_REG_PMPADDR15, &pmpaddr[15]);

  uint32_t mseccfg;
  CSR_READ(CSR_REG_MSECCFG, &mseccfg);

  LOG_INFO("=== Hardware ePMP State ===");

  for (int i = 0; i < 16; ++i) {
    uint32_t addr = pmpaddr[i];
    uint32_t cfg_reg = pmpcfg[i / 4];
    uint8_t cfg = (cfg_reg >> ((i % 4) * 8)) & 0xFF;

    int r = (cfg & 0x01) != 0;
    int w = (cfg & 0x02) != 0;
    int x = (cfg & 0x04) != 0;
    int l = (cfg & 0x80) != 0;

    uint8_t mode_bits = (cfg >> 3) & 0x03;

    if (mode_bits == 0) {
      LOG_INFO("Entry %2d: OFF", i);
    } else {
      const char *mode_str;
      switch (mode_bits) {
        case 1:
          mode_str = "TOR  ";
          break;
        case 2:
          mode_str = "NA4  ";
          break;
        case 3:
          mode_str = "NAPOT";
          break;
        default:
          mode_str = "UNKN ";
          break;
      }

      char perms[4] = {r ? 'R' : '-', w ? 'W' : '-', x ? 'X' : '-', '\0'};

      LOG_INFO("Entry %2d: %s | Addr=0x%08x | Mode=%s | Locked=%d", i, perms,
               addr, mode_str, l);
    }
  }
  LOG_INFO("MSECCFG: 0x%08x", mseccfg);
  LOG_INFO("===========================");

  return OK_STATUS();
}

status_t handle_boot_fi_init(ujson_t *uj) {
  // Configure the device.
  pentest_setup_device(uj, true, false);

  pentest_select_trigger_type(kPentestTriggerTypeSw);
  pentest_init(kPentestTriggerSourceAes,
               kPentestPeripheralIoDiv4 | kPentestPeripheralEdn |
                   kPentestPeripheralCsrng | kPentestPeripheralEntropy |
                   kPentestPeripheralKmac | kPentestPeripheralHmac);

  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  return OK_STATUS();
}

status_t handle_boot_fi(ujson_t *uj) {
  boot_fi_subcommand_t cmd;
  TRY(ujson_deserialize_boot_fi_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kBootFiSubcommandInit:
      return handle_boot_fi_init(uj);
    case kBootFiSubcommandInactiveFirmwareInvalidate:
      return handle_inactive_firmware_invalidation(uj);
    case kBootFiSubcommandNextSlot:
      return handle_next_boot_slot(uj);
    case kBootFiSubcommandBootStatus:
      return handle_boot_status(uj);
    case kBootFiSubcommandEpmpStatus:
      return handle_epmp_status(uj);
    default:
      LOG_ERROR("Unrecognized Boot FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
