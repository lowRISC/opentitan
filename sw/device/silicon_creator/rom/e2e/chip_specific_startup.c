// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/json/chip_specific_startup.h"

#include <stdbool.h>

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"

#include "csrng_regs.h"
#include "edn_regs.h"
#include "entropy_src_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "lc_ctrl_regs.h"  // Generated.
#include "otp_ctrl_regs.h"
#include "sensor_ctrl_regs.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kAstInitEnOffset = OTP_CTRL_PARAM_CREATOR_SW_CFG_AST_INIT_EN_OFFSET -
                     OTP_CTRL_PARAM_CREATOR_SW_CFG_OFFSET,
  kJitterEnOffset = OTP_CTRL_PARAM_CREATOR_SW_CFG_JITTER_EN_OFFSET -
                    OTP_CTRL_PARAM_CREATOR_SW_CFG_OFFSET,
};

void epmp_read(rom_epmp_config_t *epmp) {
  // Sadly, CSR reads must use constants for the register name.
  CSR_READ(CSR_REG_MSECCFG, &epmp->mseccfg);
  CSR_READ(CSR_REG_PMPCFG0, &epmp->cfg[0]);
  CSR_READ(CSR_REG_PMPCFG1, &epmp->cfg[1]);
  CSR_READ(CSR_REG_PMPCFG2, &epmp->cfg[2]);
  CSR_READ(CSR_REG_PMPCFG3, &epmp->cfg[3]);
  CSR_READ(CSR_REG_PMPADDR0, &epmp->addr[0]);
  CSR_READ(CSR_REG_PMPADDR1, &epmp->addr[1]);
  CSR_READ(CSR_REG_PMPADDR2, &epmp->addr[2]);
  CSR_READ(CSR_REG_PMPADDR3, &epmp->addr[3]);
  CSR_READ(CSR_REG_PMPADDR4, &epmp->addr[4]);
  CSR_READ(CSR_REG_PMPADDR5, &epmp->addr[5]);
  CSR_READ(CSR_REG_PMPADDR6, &epmp->addr[6]);
  CSR_READ(CSR_REG_PMPADDR7, &epmp->addr[7]);
  CSR_READ(CSR_REG_PMPADDR8, &epmp->addr[8]);
  CSR_READ(CSR_REG_PMPADDR9, &epmp->addr[9]);
  CSR_READ(CSR_REG_PMPADDR10, &epmp->addr[10]);
  CSR_READ(CSR_REG_PMPADDR11, &epmp->addr[11]);
  CSR_READ(CSR_REG_PMPADDR12, &epmp->addr[12]);
  CSR_READ(CSR_REG_PMPADDR13, &epmp->addr[13]);
  CSR_READ(CSR_REG_PMPADDR14, &epmp->addr[14]);
  CSR_READ(CSR_REG_PMPADDR15, &epmp->addr[15]);
}

void entropy_config_read(rom_entropy_config_t *entropy) {
  // We read the entropy and rng configs directly from the peripherals because
  // we want to evaluate the mubi values in the test harness.
  mmio_region_t entropy_src =
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR);
  mmio_region_t csrng = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR);
  mmio_region_t edn = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR);

  entropy->entropy_src =
      mmio_region_read32(entropy_src, ENTROPY_SRC_CONF_REG_OFFSET);
  entropy->csrng = mmio_region_read32(csrng, CSRNG_CTRL_REG_OFFSET);
  entropy->edn = mmio_region_read32(edn, EDN_CTRL_REG_OFFSET);
}

status_t test_chip_specific_startup(ujson_t *uj) {
  dif_sram_ctrl_t sram_ctrl;
  dif_otp_ctrl_t otp_ctrl;
  dif_lc_ctrl_t lc;
  dif_clkmgr_t clkmgr;

  LOG_INFO("Initializing DIFs");
  TRY(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR),
      &sram_ctrl));
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  TRY(dif_lc_ctrl_init(mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR),
                       &lc));
  TRY(dif_clkmgr_init(mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR),
                      &clkmgr));

  LOG_INFO("Querying hardware");
  // We need to know about lifecycle state, jitter and SRAM configuration.
  dif_lc_ctrl_state_t lc_state;
  TRY(dif_lc_ctrl_get_state(&lc, &lc_state));

  dif_toggle_t jitter;
  TRY(dif_clkmgr_jitter_get_enabled(&clkmgr, &jitter));

  dif_sram_ctrl_status_bitfield_t sram;
  TRY(dif_sram_ctrl_get_status(&sram_ctrl, &sram));

  chip_startup_t cs = {
      .lc_state = lc_state,
      .jitter = (jitter == kDifToggleEnabled),
      .sram =
          {
              .scr_key_valid = (sram & kDifSramCtrlStatusScrKeyValid) != 0,
              .scr_key_seed_valid =
                  (sram & kDifSramCtrlStatusScrKeySeedValid) != 0,
              .init_done = (sram & kDifSramCtrlStatusInitDone) != 0,
          },
  };

  // We need to know the OTP configs for AST init and jitter in order to
  // correctly determine the pass/fail conditions.
  TRY(dif_otp_ctrl_read_blocking(&otp_ctrl, kDifOtpCtrlPartitionCreatorSwCfg,
                                 kAstInitEnOffset,
                                 &cs.otp.creator_sw_cfg_ast_init_en, 1));
  TRY(dif_otp_ctrl_read_blocking(&otp_ctrl, kDifOtpCtrlPartitionCreatorSwCfg,
                                 kJitterEnOffset,
                                 &cs.otp.creator_sw_cfg_jitter_en, 1));

  // Read the entropy config directly from the peripherals.  The DIFs don't
  // currently do this and we care about the mubi values.
  entropy_config_read(&cs.entropy);

  // Read out the raw ePMP configuration.  The test harness will evaluate it
  // for correctness based on the lifecycle state.
  epmp_read(&cs.epmp);

  // Read out the AST_DONE bit.  The test harness will evaluate it for
  // correctness based on the OTP configuration.
  mmio_region_t sensor_ctrl =
      mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR);
  cs.ast_init_done = bitfield_bit32_read(
      mmio_region_read32(sensor_ctrl, SENSOR_CTRL_STATUS_REG_OFFSET),
      SENSOR_CTRL_STATUS_AST_INIT_DONE_BIT);
  // Read out the `mstatus` CSR.  The test harness will evaluate it for
  // correctness.
  CSR_READ(CSR_REG_MSTATUS, &cs.mstatus);

  // Return the chip startup information to the test harness as json.
  RESP_OK(ujson_serialize_chip_startup_t, uj, &cs);
  return OK_STATUS();
}

status_t command_processor(ujson_t *uj) {
  while (true) {
    test_command_t command;
    TRY(ujson_deserialize_test_command_t(uj, &command));
    switch (command) {
      case kTestCommandChipStartup:
        RESP_ERR(uj, test_chip_specific_startup(uj));
        break;
      default:
        LOG_ERROR("Unrecognized command: %d", command);
        RESP_ERR(uj, INVALID_ARGUMENT());
    }
  }
  return OK_STATUS(0);
}

bool test_main(void) {
  ujson_t uj = ujson_ottf_console();
  return status_ok(command_processor(&uj));
}
