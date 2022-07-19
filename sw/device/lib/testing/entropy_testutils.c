// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "edn_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static void setup_entropy_src(void) {
  dif_entropy_src_t entropy_src;
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));

  // Disable entropy for test purpose, as it has been turned on by ROM
  CHECK_DIF_OK(dif_entropy_src_set_enabled(&entropy_src, kDifToggleDisabled));

  const dif_entropy_src_config_t config = {
      .fips_enable = true,
      .route_to_firmware = false,
      .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
  };
  CHECK_DIF_OK(
      dif_entropy_src_configure(&entropy_src, config, kDifToggleEnabled));
}

static void setup_csrng(void) {
  dif_csrng_t csrng;
  CHECK_DIF_OK(dif_csrng_init(
      mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng));

  CHECK_DIF_OK(dif_csrng_stop(&csrng));
  CHECK_DIF_OK(dif_csrng_configure(&csrng));
}

static void setup_edn(bool auto_mode) {
  // Temporary solution to configure/enable the EDN and CSRNG to allow OTBN to
  // run before a DIF is available,
  // https://github.com/lowRISC/opentitan/issues/6082
  // disable edn.
  uint32_t reg = 0;
  reg =
      bitfield_field32_write(0, EDN_CTRL_EDN_ENABLE_FIELD, kMultiBitBool4False);
  reg = bitfield_field32_write(reg, EDN_CTRL_BOOT_REQ_MODE_FIELD,
                               kMultiBitBool4False);
  reg = bitfield_field32_write(reg, EDN_CTRL_AUTO_REQ_MODE_FIELD,
                               kMultiBitBool4False);
  reg = bitfield_field32_write(reg, EDN_CTRL_CMD_FIFO_RST_FIELD,
                               kMultiBitBool4False);
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR),
                      EDN_CTRL_REG_OFFSET, reg);

  if (auto_mode) {
    dif_edn_t edn0, edn1;

    // temporarily declare handle in here, should fix later
    CHECK_DIF_OK(dif_edn_init(
        mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));
    CHECK_DIF_OK(dif_edn_init(
        mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn1));

    dif_edn_seed_material_t inst_cmd = {.len = 1,
                                        .data = {kDifEdnCmdInstantiate}};

    dif_edn_seed_material_t reseed_cmd = {.len = 1, .data = {kDifEdnCmdReseed}};

    dif_edn_seed_material_t generate_cmd = {
        .len = 1, .data = {0xf000 | kDifEdnCmdGenerate}};

    dif_edn_auto_params_t edn0_params = {.reseed_material = reseed_cmd,
                                         .generate_material = generate_cmd,
                                         .reseed_interval = 1 << 31};

    dif_edn_auto_params_t edn1_params = {.reseed_material = reseed_cmd,
                                         .generate_material = generate_cmd,
                                         .reseed_interval = 1};

    // setup edn parameters
    CHECK_DIF_OK(dif_edn_set_auto_mode(&edn0, edn0_params));
    CHECK_DIF_OK(dif_edn_set_auto_mode(&edn1, edn1_params));

    // enable
    CHECK_DIF_OK(dif_edn_configure(&edn0));
    CHECK_DIF_OK(dif_edn_configure(&edn1));

    // instantiate csrng instances
    CHECK_DIF_OK(
        dif_edn_instantiate(&edn0, kDifEdnEntropySrcToggleEnable, &inst_cmd));
    CHECK_DIF_OK(
        dif_edn_instantiate(&edn1, kDifEdnEntropySrcToggleEnable, &inst_cmd));

  } else {
    reg = bitfield_field32_write(0, EDN_CTRL_EDN_ENABLE_FIELD,
                                 kMultiBitBool4True);
    reg = bitfield_field32_write(reg, EDN_CTRL_BOOT_REQ_MODE_FIELD,
                                 kMultiBitBool4True);
    reg = bitfield_field32_write(reg, EDN_CTRL_AUTO_REQ_MODE_FIELD,
                                 kMultiBitBool4False);
    reg = bitfield_field32_write(reg, EDN_CTRL_CMD_FIFO_RST_FIELD,
                                 kMultiBitBool4False);
    mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR),
                        EDN_CTRL_REG_OFFSET, reg);
    mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR),
                        EDN_CTRL_REG_OFFSET, reg);
  }
}

void entropy_testutils_boot_mode_init(void) {
  setup_entropy_src();
  setup_csrng();
  setup_edn(false);
}

void entropy_testutils_auto_mode_init(void) {
  setup_entropy_src();
  setup_csrng();
  setup_edn(true);
}

void entropy_testutils_wait_for_state(const dif_entropy_src_t *entropy_src,
                                      dif_entropy_src_main_fsm_t state) {
  dif_entropy_src_main_fsm_t cur_state;

  do {
    CHECK_DIF_OK(dif_entropy_src_get_main_fsm_state(entropy_src, &cur_state));
  } while (cur_state != state);
}
