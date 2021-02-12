// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/pmp.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/stdasm.h"

// "Volume II: RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified",
// "3.6.1 Physical Memory Protection CSRs",
// "Figure 3.28: PMP configuration register format".
#define PMP_CFG_CSR_R 0
#define PMP_CFG_CSR_W 1
#define PMP_CFG_CSR_X 2
#define PMP_CFG_CSR_A 3
#define PMP_CFG_CSR_L 7

#define PMP_CFG_FIELDS_PER_REG 4
#define PMP_CFG_FIELD_WIDTH 8
#define PMP_CFG_FIELD_MASK 0xff

// "Volume II: RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified",
// "3.6.1 Physical Memory Protection CSRs", "Address Matching".
#define PMP_CFG_CSR_MODE_OFF 0
#define PMP_CFG_CSR_MODE_TOR 1
#define PMP_CFG_CSR_MODE_NA4 2
#define PMP_CFG_CSR_MODE_NAPOT 3
#define PMP_CFG_CSR_MODE_MASK 0x3

typedef enum pmp_csr_access_type {
  kPmpCsrAccessTypeRead = 0,
  kPmpCsrAccessTypeWrite,
} pmp_csr_access_type_t;

static const bitfield_field32_t kPmpCfgModeField = {
    .mask = PMP_CFG_CSR_MODE_MASK, .index = PMP_CFG_CSR_A,
};

/**
 * Reads the pmpcfg for a given region.
 *
 * This reads the entire `pmpcfgN` value, not just the word associated with the
 * current region.
 *
 * @param region PMP Region ID to read.
 * @param[out] value Where to put the result of the read.
 * @return `true` if `pmp_region_index_t` is valid and value was read, `false`
 * otherwise.
 */
PMP_WARN_UNUSED_RESULT
static bool pmp_cfg_csr_read(pmp_region_index_t region, uint32_t *value) {
  switch (region) {
#define PMP_REGION(region_id, config_reg_id)                               \
  case region_id: {                                                        \
    uint32_t read_value;                                                   \
    asm volatile("csrr %0, pmpcfg" #config_reg_id ";" : "=r"(read_value)); \
    *value = read_value;                                                   \
    return true;                                                           \
  }
#include "sw/device/lib/runtime/pmp_regions.def"
    default:
      return false;
  }
}

/**
 * Writes the pmpcfg for a given region.
 *
 * This writes the entire `pmpcfgN` value, not just the word associated with the
 * current region.
 *
 * @param region PMP Region ID to write.
 * @param value the value to write.
 * @return `true` if `pmp_region_index_t` is valid and value was written,
 * `false` otherwise.
 */
PMP_WARN_UNUSED_RESULT
static bool pmp_cfg_csr_write(pmp_region_index_t region, uint32_t value) {
  switch (region) {
#define PMP_REGION(region_id, config_reg_id)                         \
  case region_id: {                                                  \
    asm volatile("csrw pmpcfg" #config_reg_id ", %0;" ::"r"(value)); \
    return true;                                                     \
  }
#include "sw/device/lib/runtime/pmp_regions.def"
    default:
      return false;
  }
}

/**
 * Reads the pmpaddr for a given region.
 *
 * @param region PMP Region ID to read.
 * @param[out] value Where to put the result of the read.
 * @return `true` if `pmp_region_index_t` is valid and value was read, `false`
 * otherwise.
 */
PMP_WARN_UNUSED_RESULT
static bool pmp_addr_csr_read(pmp_region_index_t region, uint32_t *value) {
  switch (region) {
#define PMP_REGION(region_id, _)                                    \
  case region_id: {                                                 \
    asm volatile("csrr %0, pmpaddr" #region_id ";" : "=r"(*value)); \
    return true;                                                    \
  }
#include "sw/device/lib/runtime/pmp_regions.def"
    default:
      return false;
  }
}

/**
 * Writes the pmpcfg for a given region.
 *
 * @param region PMP region ID to get/set.
 * @param value Value to write into a CSR.
 * @return `pmp_region_configure_result_t`.
 */
PMP_WARN_UNUSED_RESULT
static bool pmp_addr_csr_write(pmp_region_index_t region, uint32_t value) {
  switch (region) {
#define PMP_REGION(region_id, _)                                    \
  case region_id: {                                                 \
    asm volatile("csrw pmpaddr" #region_id ", %0;" : : "r"(value)); \
    return true;                                                    \
  }
#include "sw/device/lib/runtime/pmp_regions.def"
    default:
      return false;
  }
}

/**
 * Retrievs configuration information for the requested `region`.
 *
 * A single `pmpcfg` CSR packs configuration information for `N` regions.
 *
 * @param region PMP region ID.
 * @param field_value Configuration information for the `region`.
 * @return `pmp_region_configure_result_t`.
 */
PMP_WARN_UNUSED_RESULT
static pmp_region_configure_result_t pmp_csr_cfg_field_read(
    pmp_region_index_t region, uint32_t *field_value) {
  uint32_t cfg_csr_original;
  if (!pmp_cfg_csr_read(region, &cfg_csr_original)) {
    return kPmpRegionConfigureError;
  }

  size_t field_index = (region % PMP_CFG_FIELDS_PER_REG) * PMP_CFG_FIELD_WIDTH;
  bitfield_field32_t pmp_csr_cfg_field = {
      .mask = PMP_CFG_FIELD_MASK, .index = field_index,
  };

  *field_value = bitfield_field32_read(cfg_csr_original, pmp_csr_cfg_field);

  return kPmpRegionConfigureOk;
}

/**
 * Writes configuration information for the requested `region`.
 *
 * A single `pmpcfg` CSR packs configuration information for `N` regions.
 *
 * @param region PMP region ID.
 * @param field_value Configuration information for the `region`.
 * @return `pmp_region_configure_result_t`.
 */
PMP_WARN_UNUSED_RESULT
static pmp_region_configure_result_t pmp_csr_cfg_field_write(
    pmp_region_index_t region, uint32_t field_value) {
  uint32_t cfg_csr_current;
  if (!pmp_cfg_csr_read(region, &cfg_csr_current)) {
    return kPmpRegionConfigureError;
  }

  // Determine the pmpcfg field index based on the `region`.
  size_t field_index = (region % PMP_CFG_FIELDS_PER_REG) * PMP_CFG_FIELD_WIDTH;
  bitfield_field32_t pmp_csr_cfg_field = {
      .mask = PMP_CFG_FIELD_MASK, .index = field_index,
  };

  uint32_t cfg_csr_new =
      bitfield_field32_write(cfg_csr_current, pmp_csr_cfg_field, field_value);

  if (!pmp_cfg_csr_write(region, cfg_csr_new)) {
    return kPmpRegionConfigureError;
  }

  if (!pmp_cfg_csr_read(region, &cfg_csr_current)) {
    return kPmpRegionConfigureError;
  }

  if (cfg_csr_current != cfg_csr_new) {
    return kPmpRegionConfigureWarlError;
  }

  return kPmpRegionConfigureOk;
}

/**
 * Writes `address` to a pmpaddr CSRs.
 *
 * The corresponding pmpaddrN index N is determined by `region`.
 *
 * PMP address must be at least 4bytes aligned, and pmpaddr holds only bits
 * 33:2. This means that before writing an address to a pmpaddr CSR, it must be
 * shifted 2 bits to the right.
 *
 * Please see:
 * "Volume II: RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified",
 * "3.6.1 Physical Memory Protection CSRs",
 * "Figure 3.26: PMP address register format, RV32".
 *
 * @param region PMP region to configure and set address for.
 * @param address Address to be set.
 * @return `pmp_region_configure_result_t`.
 */
pmp_region_configure_result_t pmp_csr_address_write(pmp_region_index_t region,
                                                    uintptr_t address) {
  uint32_t address_shifted = address >> PMP_ADDRESS_SHIFT;
  if (!pmp_addr_csr_write(region, address_shifted)) {
    return kPmpRegionConfigureError;
  }

  uint32_t addr_csr_after_write;
  if (!pmp_addr_csr_read(region, &addr_csr_after_write)) {
    return kPmpRegionConfigureError;
  }

  if (address_shifted != addr_csr_after_write) {
    return kPmpRegionConfigureWarlError;
  }

  return kPmpRegionConfigureOk;
}

/**
 * Set PMP region permissions.
 *
 * @param perm Memory access permissions.
 * @param bitfield Bitfield to set.
 * @return `true` on success, `false` on failure.
 */
PMP_WARN_UNUSED_RESULT
static bool pmp_cfg_permissions_set(pmp_region_permissions_t perm,
                                    uint32_t *bitfield) {
  switch (perm) {
    case kPmpRegionPermissionsNone:
      // No access is allowed.
      break;
    case kPmpRegionPermissionsReadOnly:
      *bitfield = bitfield_bit32_write(*bitfield, PMP_CFG_CSR_R, true);
      break;
    case kPmpRegionPermissionsExecuteOnly:
      *bitfield = bitfield_bit32_write(*bitfield, PMP_CFG_CSR_X, true);
      break;
    case kPmpRegionPermissionsReadExecute:
      *bitfield = bitfield_bit32_write(*bitfield, PMP_CFG_CSR_R, true);
      *bitfield = bitfield_bit32_write(*bitfield, PMP_CFG_CSR_X, true);
      break;
    case kPmpRegionPermissionsReadWrite:
      *bitfield = bitfield_bit32_write(*bitfield, PMP_CFG_CSR_R, true);
      *bitfield = bitfield_bit32_write(*bitfield, PMP_CFG_CSR_W, true);
      break;
    case kPmpRegionPermissionsReadWriteExecute:
      *bitfield = bitfield_bit32_write(*bitfield, PMP_CFG_CSR_R, true);
      *bitfield = bitfield_bit32_write(*bitfield, PMP_CFG_CSR_W, true);
      *bitfield = bitfield_bit32_write(*bitfield, PMP_CFG_CSR_X, true);
      break;
    default:
      return false;
  }

  return true;
}

/**
 * Set PMP region lock.
 *
 * @param lock Lock to indicate whether the region must be locked.
 * @param bitfield Bitfield to set.
 */
static void pmp_cfg_mode_lock_set(pmp_region_lock_t lock, uint32_t *bitfield) {
  bool flag = (lock == kPmpRegionLockLocked) ? true : false;
  *bitfield = bitfield_bit32_write(*bitfield, PMP_CFG_CSR_L, flag);
}

/**
 * Check whether `address` is correctly aligned.
 *
 * The alignment depend on the granularity, which is implementation specific,
 * and for Ibex is `PMP_GRANULARITY_IBEX`. Default granularity "G" is 0, which
 * means a minimal alignment of 4bytes. Please see:
 * "Volume II: RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified",
 * "3.6 Physical Memory Protection", "Figure 3.26" and section
 * "Address Matching".
 *
 * @param address System address.
 * @return `true` on success, `false` on failure.
 */
static bool pmp_address_aligned(uintptr_t address) {
  return address == (address & PMP_ADDRESS_ALIGNMENT_INVERTED_MASK);
}

/**
 * Constructs a NAPOT address from the requested system address and size.
 *
 * This function makes sure that the `address` and `size` are valid, and then
 * constructs a corresponding NAPOT address. Please see:
 * "Volume II: RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified",
 * "3.6 Physical Memory Protection", "Figure 3.26" and "Table 3.10".
 *
 * @param address Conventional system address.
 * @param size The size of a range to protect.
 * @param pmp_address_napot Constructed NAPOT address.
 * @return `pmp_region_configure_napot_result_t`.
 */
PMP_WARN_UNUSED_RESULT
static pmp_region_configure_napot_result_t pmp_napot_address_construct(
    uintptr_t address, uint32_t size, uintptr_t *pmp_address_napot) {
  // Must be at least the size of the minimal alignment adjusted for
  // granularity, and the minimal allowed size for the NAPOT mode.
  if (size < PMP_ADDRESS_ALIGNMENT || size < PMP_ADDRESS_MIN_ALIGNMENT_NAPOT) {
    return kPmpRegionConfigureNapotBadAddress;
  }

  // Check if the `size` is a Power Of Two.
  uint32_t size_mask = size - 1;
  if ((size & size_mask) != 0) {
    return kPmpRegionConfigureNapotBadSize;
  }

  // Check if the address is aligned to the `size`.
  if (address != (address & (~size_mask))) {
    return kPmpRegionConfigureNapotBadAddress;
  }

  // `size_mask` must be right shifted, as the minimal legal size in NAPOT
  // mode is 8 bytes.
  *pmp_address_napot = address | (size_mask >> 1);

  return kPmpRegionConfigureNapotOk;
}

pmp_region_configure_result_t pmp_region_configure_off(
    pmp_region_index_t region, uintptr_t address) {
  if (region >= PMP_REGIONS_NUM) {
    return kPmpRegionConfigureBadRegion;
  }

  if (!pmp_address_aligned(address)) {
    return kPmpRegionConfigureBadAddress;
  }

  // Address registers must be written prior to the configuration registers to
  // ensure that they are not locked.
  pmp_region_configure_result_t result = pmp_csr_address_write(region, address);
  if (result != kPmpRegionConfigureOk) {
    return result;
  }

  // Clear the appropriate region field of the pmpcfg CSR.
  result = pmp_csr_cfg_field_write(region, 0);
  if (result != kPmpRegionConfigureOk) {
    return result;
  }

  return kPmpRegionConfigureOk;
}

pmp_region_configure_na4_result_t pmp_region_configure_na4(
    pmp_region_index_t region, pmp_region_config_t config, uintptr_t address) {
  if (PMP_GRANULARITY_IBEX > 0) {
    return kPmpRegionConfigureNa4Unavailable;
  }

  if (region >= PMP_REGIONS_NUM) {
    return kPmpRegionConfigureNa4BadRegion;
  }

  if (!pmp_address_aligned(address)) {
    return kPmpRegionConfigureNa4BadAddress;
  }

  uint32_t field_value = 0;
  if (!pmp_cfg_permissions_set(config.permissions, &field_value)) {
    return kPmpRegionConfigureNa4Error;
  }

  pmp_cfg_mode_lock_set(config.lock, &field_value);

  field_value = bitfield_field32_write(field_value, kPmpCfgModeField,
                                       PMP_CFG_CSR_MODE_NA4);

  // Address registers must be written prior to the configuration registers to
  // ensure that they are not locked.
  pmp_region_configure_result_t result = pmp_csr_address_write(region, address);
  if (result != kPmpRegionConfigureOk) {
    return (pmp_region_configure_na4_result_t)result;
  }

  result = pmp_csr_cfg_field_write(region, field_value);
  if (result != kPmpRegionConfigureOk) {
    return (pmp_region_configure_na4_result_t)result;
  }

  return kPmpRegionConfigureNa4Ok;
}

pmp_region_configure_napot_result_t pmp_region_configure_napot(
    pmp_region_index_t region, pmp_region_config_t config, uintptr_t address,
    uint32_t size) {
  if (region >= PMP_REGIONS_NUM) {
    return kPmpRegionConfigureNapotBadRegion;
  }

  uintptr_t napot_address;
  pmp_region_configure_napot_result_t napot_result =
      pmp_napot_address_construct(address, size, &napot_address);
  if (napot_result != kPmpRegionConfigureNapotOk) {
    return napot_result;
  }

  uint32_t field_value = 0;
  if (!pmp_cfg_permissions_set(config.permissions, &field_value)) {
    return kPmpRegionConfigureNapotError;
  }

  pmp_cfg_mode_lock_set(config.lock, &field_value);

  field_value = bitfield_field32_write(field_value, kPmpCfgModeField,
                                       PMP_CFG_CSR_MODE_NAPOT);

  // Address registers must be written prior to the configuration registers to
  // ensure that they are not locked.
  pmp_region_configure_result_t result =
      pmp_csr_address_write(region, napot_address);
  if (result != kPmpRegionConfigureOk) {
    return (pmp_region_configure_napot_result_t)result;
  }

  result = pmp_csr_cfg_field_write(region, field_value);
  if (result != kPmpRegionConfigureOk) {
    return (pmp_region_configure_napot_result_t)result;
  }

  return kPmpRegionConfigureNapotOk;
}

pmp_region_configure_result_t pmp_region_configure_tor(
    pmp_region_index_t region_end, pmp_region_config_t config,
    uintptr_t address_start, uintptr_t address_end) {
  if (region_end >= PMP_REGIONS_NUM) {
    return kPmpRegionConfigureBadRegion;
  }

  if (region_end == 0 && address_start > 0) {
    return kPmpRegionConfigureBadAddress;
  }

  if (region_end > 0 && !pmp_address_aligned(address_start)) {
    return kPmpRegionConfigureBadAddress;
  }

  if (!pmp_address_aligned(address_end)) {
    return kPmpRegionConfigureBadAddress;
  }

  uint32_t field_value = 0;
  if (!pmp_cfg_permissions_set(config.permissions, &field_value)) {
    return kPmpRegionConfigureError;
  }

  pmp_cfg_mode_lock_set(config.lock, &field_value);

  field_value = bitfield_field32_write(field_value, kPmpCfgModeField,
                                       PMP_CFG_CSR_MODE_TOR);

  // Address registers must be written prior to the configuration registers to
  // ensure that they are not locked.
  if (region_end != 0) {
    pmp_region_configure_result_t result =
        pmp_csr_address_write(region_end - 1, address_start);
    if (result != kPmpRegionConfigureOk) {
      return result;
    }
  }

  pmp_region_configure_result_t result =
      pmp_csr_address_write(region_end, address_end);
  if (result != kPmpRegionConfigureOk) {
    return result;
  }

  result = pmp_csr_cfg_field_write(region_end, field_value);
  if (result != kPmpRegionConfigureOk) {
    return result;
  }

  return kPmpRegionConfigureOk;
}

pmp_region_configure_result_t pmp_cfg_mode_lock_status_get(
    pmp_region_index_t region, pmp_region_lock_t *lock) {
  if (region >= PMP_REGIONS_NUM) {
    return kPmpRegionConfigureBadRegion;
  }

  if (lock == NULL) {
    return kPmpRegionConfigureBadArg;
  }

  uint32_t field_value;
  pmp_region_configure_result_t result =
      pmp_csr_cfg_field_read(region, &field_value);
  if (result != kPmpRegionConfigureOk) {
    return result;
  }

  bool flag = bitfield_bit32_read(field_value, PMP_CFG_CSR_L);
  *lock = flag ? kPmpRegionLockLocked : kPmpRegionLockUnlocked;

  return kPmpRegionConfigureOk;
}
