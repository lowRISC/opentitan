// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/nvm_testutils.h"

#include <string.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Chunk size for readback verification — small enough to live on the stack.
enum { kNvmMaxWordCount = 16 };

// Physical location of a logical NVM info page.
typedef struct {
  uint32_t page_id;
  uint32_t bank;
  uint32_t partition_id;
} nvm_page_phys_t;

// Mapping from nvm_info_page_t to physical flash parameters.
// Update this table when switching to a different NVM technology.
// clang-format off
static const nvm_page_phys_t kPageMap[] = {
    // Bank 0, pages 0-9
    [kNvmInfoPageFactoryId]            = {.page_id = 0, .bank = 0, .partition_id = 0},
    [kNvmInfoPageCreatorSecret]        = {.page_id = 1, .bank = 0, .partition_id = 0},
    [kNvmInfoPageOwnerSecret]          = {.page_id = 2, .bank = 0, .partition_id = 0},
    [kNvmInfoPageWaferAuthSecret]      = {.page_id = 3, .bank = 0, .partition_id = 0},
    [kNvmInfoPageAttestationKeySeeds]  = {.page_id = 4, .bank = 0, .partition_id = 0},
    [kNvmInfoPageOwnerReserved0]       = {.page_id = 5, .bank = 0, .partition_id = 0},
    [kNvmInfoPageOwnerReserved1]       = {.page_id = 6, .bank = 0, .partition_id = 0},
    [kNvmInfoPageOwnerReserved2]       = {.page_id = 7, .bank = 0, .partition_id = 0},
    [kNvmInfoPageOwnerReserved3]       = {.page_id = 8, .bank = 0, .partition_id = 0},
    [kNvmInfoPageFactoryCerts]         = {.page_id = 9, .bank = 0, .partition_id = 0},
    // Bank 1, pages 0-9
    [kNvmInfoPageBootData0]            = {.page_id = 0, .bank = 1, .partition_id = 0},
    [kNvmInfoPageBootData1]            = {.page_id = 1, .bank = 1, .partition_id = 0},
    [kNvmInfoPageOwnerSlot0]           = {.page_id = 2, .bank = 1, .partition_id = 0},
    [kNvmInfoPageOwnerSlot1]           = {.page_id = 3, .bank = 1, .partition_id = 0},
    [kNvmInfoPageCreatorReserved0]     = {.page_id = 4, .bank = 1, .partition_id = 0},
    [kNvmInfoPageOwnerReserved4]       = {.page_id = 5, .bank = 1, .partition_id = 0},
    [kNvmInfoPageOwnerReserved5]       = {.page_id = 6, .bank = 1, .partition_id = 0},
    [kNvmInfoPageOwnerReserved6]       = {.page_id = 7, .bank = 1, .partition_id = 0},
    [kNvmInfoPageOwnerReserved7]       = {.page_id = 8, .bank = 1, .partition_id = 0},
    [kNvmInfoPageDiceCerts]            = {.page_id = 9, .bank = 1, .partition_id = 0},
};
// clang-format on

const nvm_page_perms_t kPageReadOnly = {.read = kMultiBitBool4True,
                                        .write = kMultiBitBool4False,
                                        .erase = kMultiBitBool4False};

const nvm_page_perms_t kPageReadWrite = {.read = kMultiBitBool4True,
                                         .write = kMultiBitBool4True,
                                         .erase = kMultiBitBool4True};

const nvm_page_perms_t kPageWriteOnly = {.read = kMultiBitBool4False,
                                         .write = kMultiBitBool4True,
                                         .erase = kMultiBitBool4True};

const nvm_page_cfg_t kPageScrambleCfg = {.scrambling = kMultiBitBool4True,
                                         .ecc = kMultiBitBool4True,
                                         .he = kMultiBitBool4False};

const nvm_page_cfg_t kPagePlainCfg = {.scrambling = kMultiBitBool4False,
                                      .ecc = kMultiBitBool4True,
                                      .he = kMultiBitBool4False};

const nvm_page_cfg_t kPageRawCfg = {.scrambling = kMultiBitBool4False,
                                    .ecc = kMultiBitBool4False,
                                    .he = kMultiBitBool4False};

static status_t dif_flash_state_init(dif_flash_ctrl_state_t *flash) {
  TRY(dif_flash_ctrl_init_state(
      flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  return OK_STATUS();
}

status_t nvm_testutils_wait_for_init(void) {
  dif_flash_ctrl_state_t flash;
  TRY(dif_flash_state_init(&flash));
  TRY(flash_ctrl_testutils_wait_for_init(&flash));
  return OK_STATUS();
}

static dif_flash_ctrl_info_region_t phys_to_region(const nvm_page_phys_t *p) {
  dif_flash_ctrl_info_region_t region;
  region.bank = p->bank;
  region.partition_id = p->partition_id;
  region.page = p->page_id;
  return region;
}

static status_t info_page_get_props(dif_flash_ctrl_state_t *flash,
                                    const nvm_page_phys_t *p,
                                    dif_flash_ctrl_region_properties_t *props) {
  TRY(dif_flash_ctrl_get_info_region_properties(flash, phys_to_region(p),
                                                props));
  return OK_STATUS();
}

static status_t info_page_set_props(dif_flash_ctrl_state_t *flash,
                                    const nvm_page_phys_t *p,
                                    dif_flash_ctrl_region_properties_t props) {
  dif_flash_ctrl_info_region_t region = phys_to_region(p);
  TRY(dif_flash_ctrl_set_info_region_properties(flash, region, props));
  TRY(dif_flash_ctrl_set_info_region_enablement(flash, region,
                                                kDifToggleEnabled));
  return OK_STATUS();
}

status_t nvm_testutils_rom_init(uint32_t otp_flash_default_cfg) {
  dif_flash_ctrl_state_t flash;
  TRY(dif_flash_state_init(&flash));
  TRY(dif_flash_ctrl_start_controller_init(&flash));
  TRY(flash_ctrl_testutils_wait_for_init(&flash));
  if (otp_flash_default_cfg != 0) {
    dif_flash_ctrl_region_properties_t props;
    TRY(dif_flash_ctrl_get_default_region_properties(&flash, &props));
    props.scramble_en = bitfield_field32_read(otp_flash_default_cfg,
                                              FLASH_CTRL_OTP_FIELD_SCRAMBLING);
    props.ecc_en =
        bitfield_field32_read(otp_flash_default_cfg, FLASH_CTRL_OTP_FIELD_ECC);
    props.high_endurance_en =
        bitfield_field32_read(otp_flash_default_cfg, FLASH_CTRL_OTP_FIELD_HE);
    TRY(dif_flash_ctrl_set_default_region_properties(&flash, props));
  }
  TRY(dif_flash_ctrl_set_flash_enablement(&flash, kDifToggleEnabled));
#ifdef OPENTITAN_IS_EARLGREY
  TRY(dif_flash_ctrl_set_exec_enablement(&flash, kDifToggleEnabled));
#endif
  return OK_STATUS();
}

status_t nvm_testutils_info_page_setup(nvm_info_page_t page,
                                       nvm_page_perms_t perms,
                                       nvm_page_cfg_t cfg) {
  TRY_CHECK(page < ARRAYSIZE(kPageMap), "invalid page %d", page);
  const nvm_page_phys_t p = kPageMap[page];
  dif_flash_ctrl_state_t flash;
  TRY(dif_flash_state_init(&flash));
  dif_flash_ctrl_region_properties_t props = {
      .rd_en = perms.read,
      .prog_en = perms.write,
      .erase_en = perms.erase,
      .scramble_en = cfg.scrambling,
      .ecc_en = cfg.ecc,
      .high_endurance_en = cfg.he,
  };
  TRY(info_page_set_props(&flash, &p, props));
  return OK_STATUS();
}

status_t nvm_testutils_info_page_set(nvm_info_page_t page,
                                     nvm_page_perms_t perms,
                                     nvm_page_cfg_t cfg) {
  TRY_CHECK(page < ARRAYSIZE(kPageMap), "invalid page %d", page);
  const nvm_page_phys_t p = kPageMap[page];
  dif_flash_ctrl_state_t flash;
  TRY(dif_flash_state_init(&flash));
  dif_flash_ctrl_region_properties_t props;
  TRY(info_page_get_props(&flash, &p, &props));
  if (perms.read == kMultiBitBool4True)
    props.rd_en = kMultiBitBool4True;
  if (perms.write == kMultiBitBool4True)
    props.prog_en = kMultiBitBool4True;
  if (perms.erase == kMultiBitBool4True)
    props.erase_en = kMultiBitBool4True;
  if (cfg.scrambling == kMultiBitBool4True)
    props.scramble_en = kMultiBitBool4True;
  if (cfg.ecc == kMultiBitBool4True)
    props.ecc_en = kMultiBitBool4True;
  if (cfg.he == kMultiBitBool4True)
    props.high_endurance_en = kMultiBitBool4True;
  TRY(info_page_set_props(&flash, &p, props));
  return OK_STATUS();
}

status_t nvm_testutils_info_page_clear(nvm_info_page_t page,
                                       nvm_page_perms_t perms,
                                       nvm_page_cfg_t cfg) {
  TRY_CHECK(page < ARRAYSIZE(kPageMap), "invalid page %d", page);
  const nvm_page_phys_t p = kPageMap[page];
  dif_flash_ctrl_state_t flash;
  TRY(dif_flash_state_init(&flash));
  dif_flash_ctrl_region_properties_t props;
  TRY(info_page_get_props(&flash, &p, &props));
  if (perms.read == kMultiBitBool4True)
    props.rd_en = kMultiBitBool4False;
  if (perms.write == kMultiBitBool4True)
    props.prog_en = kMultiBitBool4False;
  if (perms.erase == kMultiBitBool4True)
    props.erase_en = kMultiBitBool4False;
  if (cfg.scrambling == kMultiBitBool4True)
    props.scramble_en = kMultiBitBool4False;
  if (cfg.ecc == kMultiBitBool4True)
    props.ecc_en = kMultiBitBool4False;
  if (cfg.he == kMultiBitBool4True)
    props.high_endurance_en = kMultiBitBool4False;
  TRY(info_page_set_props(&flash, &p, props));
  return OK_STATUS();
}

status_t nvm_testutils_write_info_page(nvm_info_page_t page,
                                       uint32_t byte_offset,
                                       const uint32_t *data, size_t word_count,
                                       bool erase_before_write, bool readback) {
  TRY_CHECK(page < ARRAYSIZE(kPageMap), "invalid page %d", page);
  const nvm_page_phys_t p = kPageMap[page];
  uint32_t address = p.page_id * NVM_BYTES_PER_PAGE + byte_offset;

  dif_flash_ctrl_state_t flash;
  TRY(dif_flash_state_init(&flash));

  if (erase_before_write) {
    TRY(flash_ctrl_testutils_erase_and_write_page(
        &flash, address, p.partition_id, data, kDifFlashCtrlPartitionTypeInfo,
        word_count));
  } else {
    TRY(flash_ctrl_testutils_write(&flash, address, p.partition_id, data,
                                   kDifFlashCtrlPartitionTypeInfo, word_count));
  }
  if (readback) {
    uint32_t rb_buf[kNvmMaxWordCount];
    size_t remaining = word_count;
    size_t chunk_offset = 0;
    while (remaining > 0) {
      size_t chunk =
          remaining < kNvmMaxWordCount ? remaining : kNvmMaxWordCount;
      TRY(flash_ctrl_testutils_read(
          &flash, address + chunk_offset * sizeof(uint32_t), p.partition_id,
          rb_buf, kDifFlashCtrlPartitionTypeInfo, chunk, 0));
      TRY_CHECK(
          memcmp(data + chunk_offset, rb_buf, chunk * sizeof(uint32_t)) == 0,
          "NVM write readback mismatch at page %d offset %d", page,
          byte_offset + chunk_offset * sizeof(uint32_t));
      chunk_offset += chunk;
      remaining -= chunk;
    }
  }
  return OK_STATUS();
}

status_t nvm_testutils_read_info_page(nvm_info_page_t page,
                                      uint32_t byte_offset, uint32_t *data,
                                      size_t word_count) {
  TRY_CHECK(page < ARRAYSIZE(kPageMap), "invalid page %d", page);
  const nvm_page_phys_t p = kPageMap[page];
  uint32_t address = p.page_id * NVM_BYTES_PER_PAGE + byte_offset;

  dif_flash_ctrl_state_t flash;
  TRY(dif_flash_state_init(&flash));

  TRY(flash_ctrl_testutils_read(&flash, address, p.partition_id, data,
                                kDifFlashCtrlPartitionTypeInfo, word_count, 0));
  return OK_STATUS();
}

status_t nvm_testutils_info_page_lock(nvm_info_page_t page, bool lock) {
  if (!lock) {
    return OK_STATUS();
  }
  TRY_CHECK(page < ARRAYSIZE(kPageMap), "invalid page %d", page);
  const nvm_page_phys_t p = kPageMap[page];
  dif_flash_ctrl_state_t flash;
  TRY(dif_flash_state_init(&flash));
  TRY(dif_flash_ctrl_lock_info_region_properties(&flash, phys_to_region(&p)));
  return OK_STATUS();
}

status_t nvm_testutils_data_region_setup(uint32_t region, uint32_t base,
                                         uint32_t size, nvm_page_perms_t perms,
                                         nvm_page_cfg_t cfg) {
  dif_flash_ctrl_state_t flash;
  TRY(dif_flash_state_init(&flash));
  dif_flash_ctrl_data_region_properties_t config = {
      .base = base,
      .size = size,
      .properties =
          {
              .rd_en = perms.read,
              .prog_en = perms.write,
              .erase_en = perms.erase,
              .scramble_en = cfg.scrambling,
              .ecc_en = cfg.ecc,
              .high_endurance_en = cfg.he,
          },
  };
  TRY(dif_flash_ctrl_set_data_region_properties(&flash, region, config));
  TRY(dif_flash_ctrl_set_data_region_enablement(&flash, region,
                                                kDifToggleEnabled));
  return OK_STATUS();
}

status_t nvm_testutils_data_region_lock(uint32_t region, bool lock) {
  if (!lock) {
    return OK_STATUS();
  }
  dif_flash_ctrl_state_t flash;
  TRY(dif_flash_state_init(&flash));
  TRY(dif_flash_ctrl_lock_data_region_properties(&flash, region));
  return OK_STATUS();
}

status_t nvm_testutils_show_faults(void) {
  dif_flash_ctrl_state_t flash;
  static const dt_flash_ctrl_t kFlashCtrlDt = 0;
  TRY(dif_flash_ctrl_init_state_from_dt(&flash, kFlashCtrlDt));
  TRY(flash_ctrl_testutils_show_faults(&flash));
  return OK_STATUS();
}

status_t nvm_testutils_default_region_setup(nvm_page_perms_t perms,
                                            nvm_page_cfg_t cfg) {
  dif_flash_ctrl_state_t flash;
  TRY(dif_flash_state_init(&flash));
  dif_flash_ctrl_region_properties_t props = {
      .rd_en = perms.read,
      .prog_en = perms.write,
      .erase_en = perms.erase,
      .scramble_en = cfg.scrambling,
      .ecc_en = cfg.ecc,
      .high_endurance_en = cfg.he,
  };
  TRY(dif_flash_ctrl_set_default_region_properties(&flash, props));
  return OK_STATUS();
}
