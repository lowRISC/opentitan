// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/nvm_testutils.h"

#include <string.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

#ifdef HAS_RRAM_CTRL
#include "sw/device/lib/dif/dif_rram_ctrl.h"
#include "sw/device/lib/testing/rram_ctrl_testutils.h"
#else
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#endif  // HAS_RRAM_CTRL

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Chunk size for readback verification — small enough to live on the stack.
enum { kNvmMaxWordCount = 16 };

#ifdef HAS_RRAM_CTRL
// RRAM controller implementation

const nvm_page_perms_t kPageReadOnly = {.read = kMultiBitBool4True,
                                        .write = kMultiBitBool4False};

const nvm_page_perms_t kPageReadWrite = {.read = kMultiBitBool4True,
                                         .write = kMultiBitBool4True};

const nvm_page_perms_t kPageWriteOnly = {.read = kMultiBitBool4False,
                                         .write = kMultiBitBool4True};

const nvm_page_cfg_t kPageScrambleCfg = {.scrambling = kMultiBitBool4True,
                                         .ecc = kMultiBitBool4True};

const nvm_page_cfg_t kPagePlainCfg = {.scrambling = kMultiBitBool4False,
                                      .ecc = kMultiBitBool4True};

const nvm_page_cfg_t kPageRawCfg = {.scrambling = kMultiBitBool4False,
                                    .ecc = kMultiBitBool4False};

// Physical location of a logical NVM info page on RRAM.
//
// RRAM has only 8 physical info pages (`emul` = 0, `page_id` 0-7), too few
// for the 20 logical nvm_info_page_t entries inherited from flash. The
// remainder are relocated onto reserved pages of the (much larger) RRAM data
// partition instead (`emul` = 1).
typedef struct {
  uint32_t page_id;
  uint32_t emul;
} nvm_page_phys_t;

// TODO(#XXXX): pages relocated onto the data partition (`emul` = 1) all share
// a single memory-protection region (`kRramRelocatedRegion`), covering
// `kRramRelocatedPageCount` reserved data pages starting at
// `kRramEmulPageBase`, with read and write always enabled and never
// locked — RRAM only has 8 configurable data regions, fewer than the 14
// relocated pages, so there is no room for per-page permissions yet. Giving
// relocated pages (or groups of them) their own protection will require
// hardware changes to add more data regions.
enum {
  kRramRelocatedRegion = 0,
  // First data-partition page reserved for relocated pages. kPageMap's
  // `page_id` values for `emul` = 1 entries are absolute data-partition page
  // indices already offset by this base.
  kRramEmulPageBase = 4064,
  kRramRelocatedPageCount = 14,
};

// Mapping from nvm_info_page_t to a physical RRAM location. Only 6 of the 8
// physical info pages are assigned so far (pages 3-4 are reserved/unused for
// now); everything else is relocated to reserved data pages starting at
// kRramEmulPageBase.
// clang-format off
static const nvm_page_phys_t kPageMap[] = {
    // Info partition
    [kNvmInfoPageFactoryId]            = {.page_id = 0, .emul = 0},
    [kNvmInfoPageAttestationKeySeeds]  = {.page_id = 1, .emul = 0},
    [kNvmInfoPageFactoryCerts]         = {.page_id = 2, .emul = 0},
    // pages 3-4 reserved/unused for now
    [kNvmInfoPageCreatorSecret]        = {.page_id = 5, .emul = 0}, // fixed in hardware
    [kNvmInfoPageOwnerSecret]          = {.page_id = 6, .emul = 0}, // fixed in hardware
    [kNvmInfoPageWaferAuthSecret]      = {.page_id = 7, .emul = 0}, // fixed in hardware
    // Data partition, reserved pages kRramEmulPageBase + 0-13
    [kNvmInfoPageOwnerReserved0]       = {.page_id = kRramEmulPageBase + 0,  .emul = 1},
    [kNvmInfoPageOwnerReserved1]       = {.page_id = kRramEmulPageBase + 1,  .emul = 1},
    [kNvmInfoPageOwnerReserved2]       = {.page_id = kRramEmulPageBase + 2,  .emul = 1},
    [kNvmInfoPageOwnerReserved3]       = {.page_id = kRramEmulPageBase + 3,  .emul = 1},
    [kNvmInfoPageBootData0]            = {.page_id = kRramEmulPageBase + 4,  .emul = 1},
    [kNvmInfoPageBootData1]            = {.page_id = kRramEmulPageBase + 5,  .emul = 1},
    [kNvmInfoPageOwnerSlot0]           = {.page_id = kRramEmulPageBase + 6,  .emul = 1},
    [kNvmInfoPageOwnerSlot1]           = {.page_id = kRramEmulPageBase + 7,  .emul = 1},
    [kNvmInfoPageCreatorReserved0]     = {.page_id = kRramEmulPageBase + 8,  .emul = 1},
    [kNvmInfoPageOwnerReserved4]       = {.page_id = kRramEmulPageBase + 9,  .emul = 1},
    [kNvmInfoPageOwnerReserved5]       = {.page_id = kRramEmulPageBase + 10, .emul = 1},
    [kNvmInfoPageOwnerReserved6]       = {.page_id = kRramEmulPageBase + 11, .emul = 1},
    [kNvmInfoPageOwnerReserved7]       = {.page_id = kRramEmulPageBase + 12, .emul = 1},
    [kNvmInfoPageDiceCerts]            = {.page_id = kRramEmulPageBase + 13, .emul = 1},
};
// clang-format on

static status_t dif_rram_state_init(dif_rram_ctrl_state_t *rram) {
  TRY(dif_rram_ctrl_init_state(
      rram, mmio_region_from_addr(TOP_EARLGREY_RRAM_CTRL_CORE_BASE_ADDR)));
  return OK_STATUS();
}

status_t nvm_testutils_wait_for_init(void) {
  dif_rram_ctrl_state_t rram;
  TRY(dif_rram_state_init(&rram));
  dif_rram_ctrl_phy_status_t phy_status;
  do {
    TRY(dif_rram_ctrl_get_phy_status(&rram, &phy_status));
  } while (!phy_status.phy_init_done);
  return OK_STATUS();
}

status_t nvm_testutils_rom_init(uint32_t otp_nvm_default_cfg) {
  dif_rram_ctrl_state_t rram;
  TRY(dif_rram_state_init(&rram));
  TRY(dif_rram_ctrl_start_controller_init(&rram));
  dif_rram_ctrl_status_t status;
  do {
    TRY(dif_rram_ctrl_get_status(&rram, &status));
  } while (!status.controller_init_done);

  // Unlike for flash_ctrl, where the memory protection only gates the
  // controller's own transaction-based (FIFO) reads/writes, the memory
  // protection regions of rram_ctrl also gate the direct read path. Hence,
  // RD_EN needs to be set in order to be able to read from RRAM.
  dif_rram_ctrl_region_properties_t props;
  TRY(dif_rram_ctrl_get_default_region_properties(&rram, &props));
  props.rd_en = kMultiBitBool4True;
  if (otp_nvm_default_cfg != 0) {
    // RRAM has no high-endurance concept, so FLASH_CTRL_OTP_FIELD_HE is not
    // applied here.
    props.scramble_en = bitfield_field32_read(otp_nvm_default_cfg,
                                              FLASH_CTRL_OTP_FIELD_SCRAMBLING);
    props.ecc_en =
        bitfield_field32_read(otp_nvm_default_cfg, FLASH_CTRL_OTP_FIELD_ECC);
  }
  TRY(dif_rram_ctrl_set_default_region_properties(&rram, props));
  TRY(dif_rram_ctrl_set_rram_enablement(&rram, kDifToggleEnabled));
  TRY(dif_rram_ctrl_set_exec_enablement(&rram, kDifToggleEnabled));
  return OK_STATUS();
}

static status_t rram_info_page_get_props(
    dif_rram_ctrl_state_t *rram, uint32_t page_id,
    dif_rram_ctrl_region_properties_t *props) {
  dif_rram_ctrl_info_region_t region = {.page = page_id};
  TRY(dif_rram_ctrl_get_info_region_properties(rram, region, props));
  return OK_STATUS();
}

static status_t rram_info_page_set_props(
    dif_rram_ctrl_state_t *rram, uint32_t page_id,
    dif_rram_ctrl_region_properties_t props) {
  return rram_ctrl_testutils_info_region_setup_properties(rram, page_id, props,
                                                          /*offset=*/NULL);
}

static status_t rram_relocated_region_enable(dif_rram_ctrl_state_t *rram,
                                             nvm_page_cfg_t cfg) {
  dif_rram_ctrl_region_properties_t properties = {
      .rd_en = kMultiBitBool4True,
      .wr_en = kMultiBitBool4True,
      .scramble_en = cfg.scrambling,
      .ecc_en = cfg.ecc,
  };
  return rram_ctrl_testutils_data_region_setup_properties(
      rram, kRramEmulPageBase, kRramRelocatedRegion, kRramRelocatedPageCount,
      properties, /*offset=*/NULL);
}

status_t nvm_testutils_info_page_setup(nvm_info_page_t page,
                                       nvm_page_perms_t perms,
                                       nvm_page_cfg_t cfg) {
  TRY_CHECK(page < ARRAYSIZE(kPageMap), "invalid page %d", page);
  const nvm_page_phys_t p = kPageMap[page];
  dif_rram_ctrl_state_t rram;
  TRY(dif_rram_state_init(&rram));
  if (p.emul != 0) {
    // `perms` is ignored: the shared region is always readable/writable.
    TRY(rram_relocated_region_enable(&rram, cfg));
    return OK_STATUS();
  }
  // RRAM has no separate erase permission or high-endurance concept, so
  // `perms.erase` and `cfg.he` are ignored here.
  dif_rram_ctrl_region_properties_t props = {
      .rd_en = perms.read,
      .wr_en = perms.write,
      .scramble_en = cfg.scrambling,
      .ecc_en = cfg.ecc,
  };
  TRY(rram_info_page_set_props(&rram, p.page_id, props));
  return OK_STATUS();
}

status_t nvm_testutils_info_page_set(nvm_info_page_t page,
                                     nvm_page_perms_t perms,
                                     nvm_page_cfg_t cfg) {
  TRY_CHECK(page < ARRAYSIZE(kPageMap), "invalid page %d", page);
  const nvm_page_phys_t p = kPageMap[page];
  dif_rram_ctrl_state_t rram;
  TRY(dif_rram_state_init(&rram));
  if (p.emul != 0) {
    // `perms` is ignored: the shared region is always readable/writable.
    TRY(rram_relocated_region_enable(&rram, cfg));
    return OK_STATUS();
  }
  dif_rram_ctrl_region_properties_t props;
  TRY(rram_info_page_get_props(&rram, p.page_id, &props));
  if (perms.read == kMultiBitBool4True) {
    props.rd_en = kMultiBitBool4True;
  }
  if (perms.write == kMultiBitBool4True) {
    props.wr_en = kMultiBitBool4True;
  }
  if (cfg.scrambling == kMultiBitBool4True) {
    props.scramble_en = kMultiBitBool4True;
  }
  if (cfg.ecc == kMultiBitBool4True) {
    props.ecc_en = kMultiBitBool4True;
  }
  TRY(rram_info_page_set_props(&rram, p.page_id, props));
  return OK_STATUS();
}

status_t nvm_testutils_info_page_clear(nvm_info_page_t page,
                                       nvm_page_perms_t perms,
                                       nvm_page_cfg_t cfg) {
  TRY_CHECK(page < ARRAYSIZE(kPageMap), "invalid page %d", page);
  const nvm_page_phys_t p = kPageMap[page];
  TRY_CHECK(p.emul == 0,
            "page %d shares mp region %d with other relocated pages; "
            "clearing permissions there would affect them too",
            page, kRramRelocatedRegion);
  dif_rram_ctrl_state_t rram;
  TRY(dif_rram_state_init(&rram));
  dif_rram_ctrl_region_properties_t props;
  TRY(rram_info_page_get_props(&rram, p.page_id, &props));
  if (perms.read == kMultiBitBool4True) {
    props.rd_en = kMultiBitBool4False;
  }
  if (perms.write == kMultiBitBool4True) {
    props.wr_en = kMultiBitBool4False;
  }
  if (cfg.scrambling == kMultiBitBool4True) {
    props.scramble_en = kMultiBitBool4False;
  }
  if (cfg.ecc == kMultiBitBool4True) {
    props.ecc_en = kMultiBitBool4False;
  }
  TRY(rram_info_page_set_props(&rram, p.page_id, props));
  return OK_STATUS();
}

status_t nvm_testutils_write_info_page(nvm_info_page_t page,
                                       uint32_t byte_offset,
                                       const uint32_t *data, size_t word_count,
                                       bool erase_before_write, bool readback) {
  TRY_CHECK(page < ARRAYSIZE(kPageMap), "invalid page %d", page);
  const nvm_page_phys_t p = kPageMap[page];
  // RRAM has no erase step; writes overwrite in place.
  (void)erase_before_write;

  dif_rram_ctrl_state_t rram;
  TRY(dif_rram_state_init(&rram));
  dif_rram_ctrl_device_info_t info = dif_rram_ctrl_get_device_info();
  dif_rram_ctrl_partition_type_t partition_type =
      p.emul == 0 ? kDifRramCtrlPartitionTypeInfo
                  : kDifRramCtrlPartitionTypeData;
  uint32_t address = p.page_id * info.bytes_per_page + byte_offset;

  // RRAM writes must start at a 16-byte-aligned address and cover a multiple
  // of 4 32-bit words (see dif_rram_ctrl_start()'s checks); unlike flash,
  // there's no "just write these bytes" primitive. Fall back to the existing
  // single-word read-modify-write helper for any misaligned/sub-4-word
  // leading or trailing words, so callers can still request an arbitrary
  // byte_offset/word_count, as flash allowed; write fully-aligned interior
  // blocks directly, in as few transactions as possible.
  enum { kRramWriteWords = 4, kRramWriteBytes = kRramWriteWords * 4 };
  size_t write_remaining = word_count;
  const uint32_t *src = data;
  uint32_t addr = address;
  while (write_remaining > 0) {
    if (addr % kRramWriteBytes == 0 && write_remaining >= kRramWriteWords) {
      size_t full_words = (write_remaining / kRramWriteWords) * kRramWriteWords;
      TRY(rram_ctrl_testutils_write(&rram, addr, src, partition_type,
                                    (uint32_t)full_words));
      addr += (uint32_t)(full_words * sizeof(uint32_t));
      src += full_words;
      write_remaining -= full_words;
      continue;
    }
    TRY(rram_ctrl_testutils_write_word(&rram, addr, src, partition_type));
    addr += sizeof(uint32_t);
    src += 1;
    write_remaining -= 1;
  }

  if (readback) {
    uint32_t rb_buf[kNvmMaxWordCount];
    size_t remaining = word_count;
    size_t chunk_offset = 0;
    while (remaining > 0) {
      size_t chunk =
          remaining < kNvmMaxWordCount ? remaining : kNvmMaxWordCount;
      TRY(rram_ctrl_testutils_read(&rram,
                                   address + chunk_offset * sizeof(uint32_t),
                                   rb_buf, partition_type, (uint32_t)chunk,
                                   /*delay_micros=*/0));
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
  dif_rram_ctrl_state_t rram;
  TRY(dif_rram_state_init(&rram));
  dif_rram_ctrl_device_info_t info = dif_rram_ctrl_get_device_info();
  dif_rram_ctrl_partition_type_t partition_type =
      p.emul == 0 ? kDifRramCtrlPartitionTypeInfo
                  : kDifRramCtrlPartitionTypeData;
  uint32_t address = p.page_id * info.bytes_per_page + byte_offset;
  TRY(rram_ctrl_testutils_read(&rram, address, data, partition_type,
                               (uint32_t)word_count, /*delay_micros=*/0));
  return OK_STATUS();
}

status_t nvm_testutils_info_page_lock(nvm_info_page_t page, bool lock) {
  if (!lock) {
    return OK_STATUS();
  }
  TRY_CHECK(page < ARRAYSIZE(kPageMap), "invalid page %d", page);
  const nvm_page_phys_t p = kPageMap[page];
  if (p.emul != 0) {
    // The shared relocated-page region is intentionally never locked (see
    // TODO above): locking it would freeze every relocated page at once.
    return OK_STATUS();
  }
  dif_rram_ctrl_state_t rram;
  TRY(dif_rram_state_init(&rram));
  dif_rram_ctrl_info_region_t region = {.page = p.page_id};
  TRY(dif_rram_ctrl_lock_info_region_properties(&rram, region));
  return OK_STATUS();
}

// `base`/`size` are in units of `NVM_BYTES_PER_PAGE`, i.e. RRAM's own page
// size; callers must not compute them from flash-specific page-size
// constants.
status_t nvm_testutils_data_region_setup(uint32_t region, uint32_t base,
                                         uint32_t size, nvm_page_perms_t perms,
                                         nvm_page_cfg_t cfg) {
  dif_rram_ctrl_state_t rram;
  TRY(dif_rram_state_init(&rram));
  // RRAM has no separate erase permission or high-endurance concept, so
  // `perms.erase` and `cfg.he` are ignored here.
  dif_rram_ctrl_data_region_properties_t config = {
      .base = base,
      .size = size,
      .properties =
          {
              .rd_en = perms.read,
              .wr_en = perms.write,
              .scramble_en = cfg.scrambling,
              .ecc_en = cfg.ecc,
          },
  };
  TRY(dif_rram_ctrl_set_data_region_properties(&rram, region, config));
  TRY(dif_rram_ctrl_set_data_region_enablement(&rram, region,
                                               kDifToggleEnabled));
  return OK_STATUS();
}

status_t nvm_testutils_data_region_lock(uint32_t region, bool lock) {
  if (!lock) {
    return OK_STATUS();
  }
  dif_rram_ctrl_state_t rram;
  TRY(dif_rram_state_init(&rram));
  TRY(dif_rram_ctrl_lock_data_region_properties(&rram, region));
  return OK_STATUS();
}

status_t nvm_testutils_data_write(uint32_t byte_address, const uint32_t *data,
                                  size_t word_count, bool erase_before_write) {
  // RRAM has no erase step; writes overwrite in place.
  (void)erase_before_write;

  dif_rram_ctrl_state_t rram;
  TRY(dif_rram_state_init(&rram));
  // See `nvm_testutils_write_info_page()` for why writes are split into
  // aligned interior blocks and single-word read-modify-writes for any
  // misaligned/sub-4-word leading or trailing words.
  enum { kRramWriteWords = 4, kRramWriteBytes = kRramWriteWords * 4 };
  size_t write_remaining = word_count;
  const uint32_t *src = data;
  uint32_t addr = byte_address;
  while (write_remaining > 0) {
    if (addr % kRramWriteBytes == 0 && write_remaining >= kRramWriteWords) {
      size_t full_words = (write_remaining / kRramWriteWords) * kRramWriteWords;
      TRY(rram_ctrl_testutils_write(&rram, addr, src,
                                    kDifRramCtrlPartitionTypeData,
                                    (uint32_t)full_words));
      addr += (uint32_t)(full_words * sizeof(uint32_t));
      src += full_words;
      write_remaining -= full_words;
      continue;
    }
    TRY(rram_ctrl_testutils_write_word(&rram, addr, src,
                                       kDifRramCtrlPartitionTypeData));
    addr += sizeof(uint32_t);
    src += 1;
    write_remaining -= 1;
  }
  return OK_STATUS();
}

status_t nvm_testutils_set_exec_enablement(bool enable) {
  dif_rram_ctrl_state_t rram;
  TRY(dif_rram_state_init(&rram));
  TRY(dif_rram_ctrl_set_exec_enablement(
      &rram, enable ? kDifToggleEnabled : kDifToggleDisabled));
  return OK_STATUS();
}

status_t nvm_testutils_show_faults(void) {
  dif_rram_ctrl_state_t rram;
  TRY(dif_rram_state_init(&rram));
  dif_rram_ctrl_faults_t faults;
  TRY(dif_rram_ctrl_get_faults(&rram, &faults));
#define LOG_IF_FIELD_SET(_struct, _field)            \
  if (_struct._field) {                              \
    LOG_INFO("Rram_ctrl fault status has " #_field); \
  }
  LOG_IF_FIELD_SET(faults, lcmgr_operation_error);
  LOG_IF_FIELD_SET(faults, lcmgr_memory_protection_error);
  LOG_IF_FIELD_SET(faults, lcmgr_read_error);
  LOG_IF_FIELD_SET(faults, lcmgr_write_error);
  LOG_IF_FIELD_SET(faults, otp_operation_error);
  LOG_IF_FIELD_SET(faults, otp_memory_protection_error);
  LOG_IF_FIELD_SET(faults, otp_read_error);
  LOG_IF_FIELD_SET(faults, otp_write_error);
#undef LOG_IF_FIELD_SET
  return OK_STATUS();
}

status_t nvm_testutils_default_region_setup(nvm_page_perms_t perms,
                                            nvm_page_cfg_t cfg) {
  dif_rram_ctrl_state_t rram;
  TRY(dif_rram_state_init(&rram));
  // RRAM has no separate erase permission or high-endurance concept, so
  // `perms.erase` and `cfg.he` are ignored here.
  dif_rram_ctrl_region_properties_t props = {
      .rd_en = perms.read,
      .wr_en = perms.write,
      .scramble_en = cfg.scrambling,
      .ecc_en = cfg.ecc,
  };
  TRY(dif_rram_ctrl_set_default_region_properties(&rram, props));
  return OK_STATUS();
}

status_t nvm_testutils_default_region_get(nvm_page_perms_t *perms,
                                          nvm_page_cfg_t *cfg) {
  dif_rram_ctrl_state_t rram;
  TRY(dif_rram_state_init(&rram));
  dif_rram_ctrl_region_properties_t props;
  TRY(dif_rram_ctrl_get_default_region_properties(&rram, &props));
  if (perms != NULL) {
    perms->read = props.rd_en;
    perms->write = props.wr_en;
    // RRAM has no separate erase permission.
    perms->erase = kMultiBitBool4False;
  }
  if (cfg != NULL) {
    cfg->scrambling = props.scramble_en;
    cfg->ecc = props.ecc_en;
    // RRAM has no high-endurance concept.
    cfg->he = kMultiBitBool4False;
  }
  return OK_STATUS();
}

#else
// Flash controller implementation

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

status_t nvm_testutils_rom_init(uint32_t otp_nvm_default_cfg) {
  dif_flash_ctrl_state_t flash;
  TRY(dif_flash_state_init(&flash));
  TRY(dif_flash_ctrl_start_controller_init(&flash));
  TRY(flash_ctrl_testutils_wait_for_init(&flash));
  if (otp_nvm_default_cfg != 0) {
    dif_flash_ctrl_region_properties_t props;
    TRY(dif_flash_ctrl_get_default_region_properties(&flash, &props));
    props.scramble_en = bitfield_field32_read(otp_nvm_default_cfg,
                                              FLASH_CTRL_OTP_FIELD_SCRAMBLING);
    props.ecc_en =
        bitfield_field32_read(otp_nvm_default_cfg, FLASH_CTRL_OTP_FIELD_ECC);
    props.high_endurance_en =
        bitfield_field32_read(otp_nvm_default_cfg, FLASH_CTRL_OTP_FIELD_HE);
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
  if (perms.read == kMultiBitBool4True) {
    props.rd_en = kMultiBitBool4True;
  }
  if (perms.write == kMultiBitBool4True) {
    props.prog_en = kMultiBitBool4True;
  }
  if (perms.erase == kMultiBitBool4True) {
    props.erase_en = kMultiBitBool4True;
  }
  if (cfg.scrambling == kMultiBitBool4True) {
    props.scramble_en = kMultiBitBool4True;
  }
  if (cfg.ecc == kMultiBitBool4True) {
    props.ecc_en = kMultiBitBool4True;
  }
  if (cfg.he == kMultiBitBool4True) {
    props.high_endurance_en = kMultiBitBool4True;
  }
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
  if (perms.read == kMultiBitBool4True) {
    props.rd_en = kMultiBitBool4False;
  }
  if (perms.write == kMultiBitBool4True) {
    props.prog_en = kMultiBitBool4False;
  }
  if (perms.erase == kMultiBitBool4True) {
    props.erase_en = kMultiBitBool4False;
  }
  if (cfg.scrambling == kMultiBitBool4True) {
    props.scramble_en = kMultiBitBool4False;
  }
  if (cfg.ecc == kMultiBitBool4True) {
    props.ecc_en = kMultiBitBool4False;
  }
  if (cfg.he == kMultiBitBool4True) {
    props.high_endurance_en = kMultiBitBool4False;
  }
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

status_t nvm_testutils_data_write(uint32_t byte_address, const uint32_t *data,
                                  size_t word_count, bool erase_before_write) {
  dif_flash_ctrl_state_t flash;
  TRY(dif_flash_state_init(&flash));
  if (erase_before_write) {
    TRY(flash_ctrl_testutils_erase_and_write_page(
        &flash, byte_address, /*partition_id=*/0, data,
        kDifFlashCtrlPartitionTypeData, (uint32_t)word_count));
  } else {
    TRY(flash_ctrl_testutils_write(&flash, byte_address, /*partition_id=*/0,
                                   data, kDifFlashCtrlPartitionTypeData,
                                   (uint32_t)word_count));
  }
  return OK_STATUS();
}

status_t nvm_testutils_set_exec_enablement(bool enable) {
  dif_flash_ctrl_state_t flash;
  TRY(dif_flash_state_init(&flash));
  TRY(dif_flash_ctrl_set_exec_enablement(
      &flash, enable ? kDifToggleEnabled : kDifToggleDisabled));
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

status_t nvm_testutils_default_region_get(nvm_page_perms_t *perms,
                                          nvm_page_cfg_t *cfg) {
  dif_flash_ctrl_state_t flash;
  TRY(dif_flash_state_init(&flash));
  dif_flash_ctrl_region_properties_t props;
  TRY(dif_flash_ctrl_get_default_region_properties(&flash, &props));
  if (perms != NULL) {
    perms->read = props.rd_en;
    perms->write = props.prog_en;
    perms->erase = props.erase_en;
  }
  if (cfg != NULL) {
    cfg->scrambling = props.scramble_en;
    cfg->ecc = props.ecc_en;
    cfg->he = props.high_endurance_en;
  }
  return OK_STATUS();
}

#endif  // HAS_RRAM_CTRL
