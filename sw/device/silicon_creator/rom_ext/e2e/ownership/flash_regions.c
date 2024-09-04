// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

dif_flash_ctrl_state_t flash_state;

const char *mubi_prop(multi_bit_bool_t val, const char *name) {
  switch (val) {
    case kMultiBitBool4True:
      return name;
    case kMultiBitBool4False:
      return "xx";
    default:
      return "uu";
  }
}

void flash_data_region_print(size_t index,
                             dif_flash_ctrl_data_region_properties_t *p,
                             bool locked) {
  LOG_INFO("data region n=%u st=%u sz=%u %s-%s-%s-%s-%s-%s %s", index, p->base,
           p->size, mubi_prop(p->properties.rd_en, "RD"),
           mubi_prop(p->properties.prog_en, "WR"),
           mubi_prop(p->properties.erase_en, "ER"),
           mubi_prop(p->properties.scramble_en, "SC"),
           mubi_prop(p->properties.ecc_en, "EC"),
           mubi_prop(p->properties.high_endurance_en, "HE"),
           locked ? "LK" : "UN");
}

void flash_info_region_print(dif_flash_ctrl_info_region_t region,
                             dif_flash_ctrl_region_properties_t *p,
                             bool locked) {
  LOG_INFO("info region bank=%u part=%u page=%u %s-%s-%s-%s-%s-%s %s",
           region.bank, region.partition_id, region.page,
           mubi_prop(p->rd_en, "RD"), mubi_prop(p->prog_en, "WR"),
           mubi_prop(p->erase_en, "ER"), mubi_prop(p->scramble_en, "SC"),
           mubi_prop(p->ecc_en, "EC"), mubi_prop(p->high_endurance_en, "HE"),
           locked ? "LK" : "UN");
}

status_t flash_regions_print(dif_flash_ctrl_state_t *f) {
  for (uint32_t i = 0; i < 8; ++i) {
    dif_flash_ctrl_data_region_properties_t p;
    bool locked;
    TRY(dif_flash_ctrl_get_data_region_properties(f, i, &p));
    TRY(dif_flash_ctrl_data_region_is_locked(f, i, &locked));
    flash_data_region_print(i, &p, locked);
  }
  for (uint32_t i = 0; i < 4; ++i) {
    dif_flash_ctrl_info_region_t region = {
        .bank = 0,
        .partition_id = 0,
        .page = 6 + i,
    };
    bool locked;
    dif_flash_ctrl_region_properties_t p;
    TRY(dif_flash_ctrl_get_info_region_properties(f, region, &p));
    TRY(dif_flash_ctrl_info_region_is_locked(f, region, &locked));
    flash_info_region_print(region, &p, locked);
  }
  return OK_STATUS();
}

bool test_main(void) {
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  status_t sts = flash_regions_print(&flash_state);

  if (status_err(sts)) {
    LOG_ERROR("flash_regions_print: %r", sts);
  }
  return status_ok(sts);
}
