// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rv_core_ibex.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/runtime/hart.h"

// #include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rv_core_ibex_regs.h"

/**
 * Error code constants of `dif_rv_core_ibex_error_status_t` are masks for the
 * bits of RV_CORE_IBEX_ERR_STATUS_REG register.
 */
static_assert(kDifRvCoreIbexErrorStatusRegisterTransmissionIntegrity ==
                  1 << RV_CORE_IBEX_ERR_STATUS_REG_INTG_ERR_BIT,
              "Layout of RV_CORE_IBEX_ERR_STATUS_REG register changed.");
static_assert(kDifRvCoreIbexErrorStatusFatalResponseIntegrity ==
                  1 << RV_CORE_IBEX_ERR_STATUS_FATAL_INTG_ERR_BIT,
              "Layout of RV_CORE_IBEX_ERR_STATUS_REG register changed.");
static_assert(kDifRvCoreIbexErrorStatusFatalInternalError ==
                  1 << RV_CORE_IBEX_ERR_STATUS_FATAL_CORE_ERR_BIT,
              "Layout of RV_CORE_IBEX_ERR_STATUS_REG register changed.");
static_assert(kDifRvCoreIbexErrorStatusRecoverableInternal ==
                  1 << RV_CORE_IBEX_ERR_STATUS_RECOV_CORE_ERR_BIT,
              "Layout of RV_CORE_IBEX_ERR_STATUS_REG register changed.");

typedef struct ibex_addr_translation_regs {
  uint32_t matching;
  uint32_t remap;
  uint32_t en;
  uint32_t lock;
} ibex_addr_translation_regs_t;

static const ibex_addr_translation_regs_t kRegsMap
    [kDifRvCoreIbexAddrTranslationSlotCount]
    [kDifRvCoreIbexAddrTranslationSlotCount] = {
        [kDifRvCoreIbexAddrTranslationSlot_0]
            [kDifRvCoreIbexAddrTranslationDBus] =
                {
                    .matching = RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET,
                    .remap = RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_OFFSET,
                    .en = RV_CORE_IBEX_DBUS_ADDR_EN_0_REG_OFFSET,
                    .lock = RV_CORE_IBEX_DBUS_REGWEN_0_REG_OFFSET,
                },
        [kDifRvCoreIbexAddrTranslationSlot_0]
            [kDifRvCoreIbexAddrTranslationIBus] =
                {
                    .matching = RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET,
                    .remap = RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET,
                    .en = RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET,
                    .lock = RV_CORE_IBEX_IBUS_REGWEN_0_REG_OFFSET,
                },
        [kDifRvCoreIbexAddrTranslationSlot_1]
            [kDifRvCoreIbexAddrTranslationDBus] =
                {
                    .matching = RV_CORE_IBEX_DBUS_ADDR_MATCHING_1_REG_OFFSET,
                    .remap = RV_CORE_IBEX_DBUS_REMAP_ADDR_1_REG_OFFSET,
                    .en = RV_CORE_IBEX_DBUS_ADDR_EN_1_REG_OFFSET,
                    .lock = RV_CORE_IBEX_DBUS_REGWEN_1_REG_OFFSET,
                },
        [kDifRvCoreIbexAddrTranslationSlot_1]
            [kDifRvCoreIbexAddrTranslationIBus] =
                {
                    .matching = RV_CORE_IBEX_IBUS_ADDR_MATCHING_1_REG_OFFSET,
                    .remap = RV_CORE_IBEX_IBUS_REMAP_ADDR_1_REG_OFFSET,
                    .en = RV_CORE_IBEX_IBUS_ADDR_EN_1_REG_OFFSET,
                    .lock = RV_CORE_IBEX_IBUS_REGWEN_1_REG_OFFSET,
                },
};

/**
 * Convert the region address and size into a natural power of two address.
 *
 * @param addr Region start address.
 * @param size region size.
 * @return Napot address
 */
static uint32_t to_napot(uint32_t addr, size_t size) {
  return addr | (size - 1) >> 1;
}

/**
 * Split a natural power of two address into a start address and size.
 *
 * @param napot Address formated in NAPOT.
 * @param size  Pointer to receive the region size.
 * @return The region start address.
 */
static uint32_t from_napot(uint32_t napot, size_t *size) {
  for (size_t i = 1; i < sizeof(uint32_t) * 8; ++i) {
    uint32_t ref = (1u << i) - 1;
    if ((napot & ref) == ref >> 1) {
      *size = 1u << i;
      break;
    }
  }
  return napot & ~((*size - 1) >> 1);
}

dif_result_t dif_rv_core_ibex_configure_addr_translation(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_addr_translation_slot_t slot,
    dif_rv_core_ibex_addr_translation_bus_t bus,
    dif_rv_core_ibex_addr_translation_mapping_t addr_map) {
  if (rv_core_ibex == NULL || slot >= kDifRvCoreIbexAddrTranslationSlotCount ||
      bus >= kDifRvCoreIbexAddrTranslationBusCount ||
      !bitfield_is_power_of_two32(addr_map.size)) {
    return kDifBadArg;
  }

  const ibex_addr_translation_regs_t regs = kRegsMap[slot][bus];

  if (mmio_region_read32(rv_core_ibex->base_addr, (ptrdiff_t)regs.lock) == 0) {
    return kDifLocked;
  }

  uint32_t mask = to_napot(addr_map.matching_addr, addr_map.size);
  mmio_region_write32(rv_core_ibex->base_addr, (ptrdiff_t)regs.matching, mask);
  mmio_region_write32(rv_core_ibex->base_addr, (ptrdiff_t)regs.remap,
                      addr_map.remap_addr);
  icache_invalidate();
  return kDifOk;
}

dif_result_t dif_rv_core_ibex_enable_addr_translation(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_addr_translation_slot_t slot,
    dif_rv_core_ibex_addr_translation_bus_t bus) {
  if (rv_core_ibex == NULL || slot >= kDifRvCoreIbexAddrTranslationSlotCount ||
      bus >= kDifRvCoreIbexAddrTranslationBusCount) {
    return kDifBadArg;
  }
  const ibex_addr_translation_regs_t regs = kRegsMap[slot][bus];
  if (mmio_region_read32(rv_core_ibex->base_addr, (ptrdiff_t)regs.lock) == 0) {
    return kDifLocked;
  }
  mmio_region_write32(rv_core_ibex->base_addr, (ptrdiff_t)regs.en, 1);
  icache_invalidate();
  return kDifOk;
}

dif_result_t dif_rv_core_ibex_disable_addr_translation(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_addr_translation_slot_t slot,
    dif_rv_core_ibex_addr_translation_bus_t bus) {
  if (rv_core_ibex == NULL || slot >= kDifRvCoreIbexAddrTranslationSlotCount ||
      bus >= kDifRvCoreIbexAddrTranslationBusCount) {
    return kDifBadArg;
  }
  const ibex_addr_translation_regs_t regs = kRegsMap[slot][bus];
  if (mmio_region_read32(rv_core_ibex->base_addr, (ptrdiff_t)regs.lock) == 0) {
    return kDifLocked;
  }
  mmio_region_write32(rv_core_ibex->base_addr, (ptrdiff_t)regs.en, 0);
  icache_invalidate();
  return kDifOk;
}

dif_result_t dif_rv_core_ibex_read_addr_translation(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_addr_translation_slot_t slot,
    dif_rv_core_ibex_addr_translation_bus_t bus,
    dif_rv_core_ibex_addr_translation_mapping_t *addr_map) {
  if (rv_core_ibex == NULL || addr_map == NULL ||
      slot >= kDifRvCoreIbexAddrTranslationSlotCount ||
      bus >= kDifRvCoreIbexAddrTranslationBusCount) {
    return kDifBadArg;
  }

  const ibex_addr_translation_regs_t regs = kRegsMap[slot][bus];

  const uint32_t reg =
      mmio_region_read32(rv_core_ibex->base_addr, (ptrdiff_t)regs.matching);
  addr_map->matching_addr = from_napot(reg, &addr_map->size);

  addr_map->remap_addr =
      mmio_region_read32(rv_core_ibex->base_addr, (ptrdiff_t)regs.remap);

  return kDifOk;
}

dif_result_t dif_rv_core_ibex_lock_addr_translation(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_addr_translation_slot_t slot,
    dif_rv_core_ibex_addr_translation_bus_t bus) {
  if (rv_core_ibex == NULL || slot >= kDifRvCoreIbexAddrTranslationSlotCount ||
      bus >= kDifRvCoreIbexAddrTranslationBusCount) {
    return kDifBadArg;
  }
  const ibex_addr_translation_regs_t regs = kRegsMap[slot][bus];

  // Only locks in case it is not locked already.
  if (mmio_region_read32(rv_core_ibex->base_addr, (ptrdiff_t)regs.lock) == 1) {
    mmio_region_write32(rv_core_ibex->base_addr, (ptrdiff_t)regs.lock, 0);
  }

  return kDifOk;
}

dif_result_t dif_rv_core_ibex_get_error_status(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_error_status_t *error_status) {
  if (rv_core_ibex == NULL || error_status == NULL) {
    return kDifBadArg;
  }

  *error_status = mmio_region_read32(rv_core_ibex->base_addr,
                                     RV_CORE_IBEX_ERR_STATUS_REG_OFFSET);

  return kDifOk;
}

dif_result_t dif_rv_core_ibex_clear_error_status(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_error_status_t error_status) {
  if (rv_core_ibex == NULL ||
      (error_status & ~(uint32_t)kDifRvCoreIbexErrorStatusAll) != 0) {
    return kDifBadArg;
  }

  mmio_region_write32(rv_core_ibex->base_addr,
                      RV_CORE_IBEX_ERR_STATUS_REG_OFFSET, error_status);

  return kDifOk;
}

dif_result_t dif_rv_core_ibex_enable_nmi(const dif_rv_core_ibex_t *rv_core_ibex,
                                         dif_rv_core_ibex_nmi_source_t nmi) {
  if (rv_core_ibex == NULL || nmi & ~(uint32_t)kDifRvCoreIbexNmiSourceAll) {
    return kDifBadArg;
  }

  uint32_t reg = 0;
  reg = bitfield_bit32_write(
      reg, RV_CORE_IBEX_NMI_ENABLE_ALERT_EN_BIT,
      (nmi & kDifRvCoreIbexNmiSourceAlert) == kDifRvCoreIbexNmiSourceAlert);
  reg = bitfield_bit32_write(
      reg, RV_CORE_IBEX_NMI_ENABLE_WDOG_EN_BIT,
      (nmi & kDifRvCoreIbexNmiSourceWdog) == kDifRvCoreIbexNmiSourceWdog);

  mmio_region_write32(rv_core_ibex->base_addr,
                      RV_CORE_IBEX_NMI_ENABLE_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_rv_core_ibex_get_nmi_state(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_nmi_state_t *nmi_state) {
  if (rv_core_ibex == NULL || nmi_state == NULL) {
    return kDifBadArg;
  }

  *nmi_state = (dif_rv_core_ibex_nmi_state_t){0};

  uint32_t reg = mmio_region_read32(rv_core_ibex->base_addr,
                                    RV_CORE_IBEX_NMI_ENABLE_REG_OFFSET);
  nmi_state->alert_enabled =
      bitfield_bit32_read(reg, RV_CORE_IBEX_NMI_ENABLE_ALERT_EN_BIT);
  nmi_state->wdog_enabled =
      bitfield_bit32_read(reg, RV_CORE_IBEX_NMI_ENABLE_WDOG_EN_BIT);

  reg = mmio_region_read32(rv_core_ibex->base_addr,
                           RV_CORE_IBEX_NMI_STATE_REG_OFFSET);
  nmi_state->alert_raised =
      bitfield_bit32_read(reg, RV_CORE_IBEX_NMI_STATE_ALERT_BIT);
  nmi_state->wdog_barked =
      bitfield_bit32_read(reg, RV_CORE_IBEX_NMI_STATE_WDOG_BIT);

  return kDifOk;
}

dif_result_t dif_rv_core_ibex_clear_nmi_state(
    const dif_rv_core_ibex_t *rv_core_ibex, dif_rv_core_ibex_nmi_source_t nmi) {
  if (rv_core_ibex == NULL || nmi & ~(uint32_t)kDifRvCoreIbexNmiSourceAll) {
    return kDifBadArg;
  }

  uint32_t reg = 0;
  reg = bitfield_bit32_write(
      reg, RV_CORE_IBEX_NMI_STATE_ALERT_BIT,
      (nmi & kDifRvCoreIbexNmiSourceAlert) == kDifRvCoreIbexNmiSourceAlert);
  reg = bitfield_bit32_write(
      reg, RV_CORE_IBEX_NMI_STATE_WDOG_BIT,
      (nmi & kDifRvCoreIbexNmiSourceWdog) == kDifRvCoreIbexNmiSourceWdog);

  mmio_region_write32(rv_core_ibex->base_addr,
                      RV_CORE_IBEX_NMI_STATE_REG_OFFSET, reg);
  return kDifOk;
}

dif_result_t dif_rv_core_ibex_get_rnd_status(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_rnd_status_t *status) {
  if (rv_core_ibex == NULL || status == NULL) {
    return kDifBadArg;
  }

  *status = mmio_region_read32(rv_core_ibex->base_addr,
                               RV_CORE_IBEX_RND_STATUS_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_rv_core_ibex_read_rnd_data(
    const dif_rv_core_ibex_t *rv_core_ibex, uint32_t *data) {
  if (rv_core_ibex == NULL || data == NULL) {
    return kDifBadArg;
  }

  *data = mmio_region_read32(rv_core_ibex->base_addr,
                             RV_CORE_IBEX_RND_DATA_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_rv_core_ibex_read_fpga_info(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_fpga_info_t *info) {
  if (rv_core_ibex == NULL || info == NULL) {
    return kDifBadArg;
  }

  *info = mmio_region_read32(rv_core_ibex->base_addr,
                             RV_CORE_IBEX_FPGA_INFO_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_rv_core_ibex_get_sw_recov_err_alert(
    const dif_rv_core_ibex_t *rv_core_ibex, bool *enabled) {
  if (rv_core_ibex == NULL || enabled == NULL) {
    return kDifBadArg;
  }
  uint32_t reg = mmio_region_read32(rv_core_ibex->base_addr,
                                    RV_CORE_IBEX_SW_RECOV_ERR_REG_OFFSET);
  *enabled = reg != kMultiBitBool4False;
  return kDifOk;
}

dif_result_t dif_rv_core_ibex_trigger_sw_recov_err_alert(
    const dif_rv_core_ibex_t *rv_core_ibex) {
  if (rv_core_ibex == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = 0;
  reg = bitfield_field32_write(reg, RV_CORE_IBEX_SW_RECOV_ERR_VAL_FIELD,
                               kMultiBitBool4True);

  mmio_region_write32(rv_core_ibex->base_addr,
                      RV_CORE_IBEX_SW_RECOV_ERR_REG_OFFSET, reg);
  return kDifOk;
}

dif_result_t dif_rv_core_ibex_get_sw_fatal_err_alert(
    const dif_rv_core_ibex_t *rv_core_ibex, bool *enabled) {
  if (rv_core_ibex == NULL || enabled == NULL) {
    return kDifBadArg;
  }
  uint32_t reg = mmio_region_read32(rv_core_ibex->base_addr,
                                    RV_CORE_IBEX_SW_FATAL_ERR_REG_OFFSET);
  *enabled = reg != kMultiBitBool4False;
  return kDifOk;
}

dif_result_t dif_rv_core_ibex_trigger_sw_fatal_err_alert(
    const dif_rv_core_ibex_t *rv_core_ibex) {
  if (rv_core_ibex == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = 0;
  reg = bitfield_field32_write(reg, RV_CORE_IBEX_SW_FATAL_ERR_VAL_FIELD,
                               kMultiBitBool4True);

  mmio_region_write32(rv_core_ibex->base_addr,
                      RV_CORE_IBEX_SW_FATAL_ERR_REG_OFFSET, reg);
  return kDifOk;
}

enum {
  kIbexCrashDumpBytesCount = sizeof(dif_rv_core_ibex_crash_dump_info_t),
  kIbexCrashDumpWordsCount = kIbexCrashDumpBytesCount / sizeof(uint32_t),
  kIbexCrashDumpStateBytesCount = sizeof(dif_rv_core_ibex_crash_dump_state_t),
  kIbexCrashDumpStateWordsCount =
      kIbexCrashDumpStateBytesCount / sizeof(uint32_t),
  kIbexCrashDumpPreviousStateBytesCount =
      sizeof(dif_rv_core_ibex_previous_crash_dump_state_t),
  kIbexCrashDumpPreviousStateWordsCount =
      kIbexCrashDumpPreviousStateBytesCount / sizeof(uint32_t),
};

dif_result_t dif_rv_core_ibex_parse_crash_dump(
    const dif_rv_core_ibex_t *rv_core_ibex, uint32_t *cpu_info,
    uint32_t cpu_info_len,
    dif_rv_core_ibex_crash_dump_info_t *crash_dump_info) {
  if (rv_core_ibex == NULL || cpu_info == NULL || crash_dump_info == NULL ||
      cpu_info_len < kIbexCrashDumpWordsCount) {
    return kDifBadArg;
  }

  memcpy(crash_dump_info, cpu_info, kIbexCrashDumpBytesCount - 1);
  crash_dump_info->double_fault =
      dif_bool_to_toggle(cpu_info[kIbexCrashDumpWordsCount - 1] == 1);

  return kDifOk;
}
