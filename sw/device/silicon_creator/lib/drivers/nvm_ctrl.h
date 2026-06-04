// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_NVM_CTRL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_NVM_CTRL_H_

// Abstraction layer over the silicon_creator flash_ctrl driver.
//
// All silicon_creator code should use nvm_ctrl_* names.  The mapping to
// flash_ctrl lives in nvm_ctrl.c.  Swapping to a different NVM technology
// (e.g. rram) only requires updating that file.

#include <limits.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

// ---------------------------------------------------------------------------
// Type aliases
// ---------------------------------------------------------------------------

typedef flash_ctrl_partition_t   nvm_ctrl_partition_t;
typedef flash_ctrl_info_page_t   nvm_ctrl_info_page_t;
typedef flash_ctrl_perms_t       nvm_ctrl_perms_t;
typedef flash_ctrl_cfg_t         nvm_ctrl_cfg_t;
typedef flash_ctrl_erase_type_t  nvm_ctrl_erase_type_t;
typedef flash_ctrl_status_t      nvm_ctrl_status_t;
typedef flash_ctrl_error_code_t  nvm_ctrl_error_code_t;
typedef flash_ctrl_region_index_t nvm_ctrl_region_index_t;

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

// Partition type constants
#define kNvmCtrlPartitionData  kFlashCtrlPartitionData
#define kNvmCtrlPartitionInfo0 kFlashCtrlPartitionInfo0
#define kNvmCtrlPartitionInfo1 kFlashCtrlPartitionInfo1
#define kNvmCtrlPartitionInfo2 kFlashCtrlPartitionInfo2

// Partition bit/field helpers
#define NVM_CTRL_PARTITION_BIT_IS_INFO      FLASH_CTRL_PARTITION_BIT_IS_INFO
#define NVM_CTRL_PARTITION_FIELD_INFO_TYPE  FLASH_CTRL_PARTITION_FIELD_INFO_TYPE

// Erase type constants
#define kNvmCtrlEraseTypePage kFlashCtrlEraseTypePage
#define kNvmCtrlEraseTypeBank kFlashCtrlEraseTypeBank

// Erased word value
enum { kNvmCtrlErasedWord = kFlashCtrlErasedWord };

// sec_mmio write-count constants
enum {
  kNvmCtrlSecMmioCertInfoPageCreatorCfg      = kFlashCtrlSecMmioCertInfoPageCreatorCfg,
  kNvmCtrlSecMmioCertInfoPageOwnerRestrict   = kFlashCtrlSecMmioCertInfoPageOwnerRestrict,
  kNvmCtrlSecMmioCertInfoPagesOwnerRestrict  = kFlashCtrlSecMmioCertInfoPagesOwnerRestrict,
  kNvmCtrlSecMmioCreatorInfoPagesLockdown    = kFlashCtrlSecMmioCreatorInfoPagesLockdown,
  kNvmCtrlSecMmioDataDefaultCfgSet           = kFlashCtrlSecMmioDataDefaultCfgSet,
  kNvmCtrlSecMmioDataDefaultPermsSet         = kFlashCtrlSecMmioDataDefaultPermsSet,
  kNvmCtrlSecMmioExecSet                     = kFlashCtrlSecMmioExecSet,
  kNvmCtrlSecMmioInfoCfgSet                  = kFlashCtrlSecMmioInfoCfgSet,
  kNvmCtrlSecMmioInfoCfgLock                 = kFlashCtrlSecMmioInfoCfgLock,
  kNvmCtrlSecMmioInfoPermsSet                = kFlashCtrlSecMmioInfoPermsSet,
  kNvmCtrlSecMmioBankErasePermsSet           = kFlashCtrlSecMmioBankErasePermsSet,
  kNvmCtrlSecMmioInit                        = kFlashCtrlSecMmioInit,
  kNvmCtrlSecMmioDataRegionProtect           = kFlashCtrlSecMmioDataRegionProtect,
  kNvmCtrlSecMmioDataRegionProtectLock       = kFlashCtrlSecMmioDataRegionProtectLock,
};

// Info pages — same X-macro interface as flash_ctrl
#define NVM_CTRL_INFO_PAGES_DEFINE(X) FLASH_CTRL_INFO_PAGES_DEFINE(X)

// kNvmCtrlInfoPage* aliases for every kFlashCtrlInfoPage* constant.
// The underlying objects are the same flash_ctrl_info_page_t structs; the
// typedef makes them compatible with nvm_ctrl_info_page_t.
#define kNvmCtrlInfoPageFactoryId             kFlashCtrlInfoPageFactoryId
#define kNvmCtrlInfoPageCreatorSecret         kFlashCtrlInfoPageCreatorSecret
#define kNvmCtrlInfoPageOwnerSecret           kFlashCtrlInfoPageOwnerSecret
#define kNvmCtrlInfoPageWaferAuthSecret       kFlashCtrlInfoPageWaferAuthSecret
#define kNvmCtrlInfoPageAttestationKeySeeds   kFlashCtrlInfoPageAttestationKeySeeds
#define kNvmCtrlInfoPageOwnerReserved0        kFlashCtrlInfoPageOwnerReserved0
#define kNvmCtrlInfoPageOwnerReserved1        kFlashCtrlInfoPageOwnerReserved1
#define kNvmCtrlInfoPageOwnerReserved2        kFlashCtrlInfoPageOwnerReserved2
#define kNvmCtrlInfoPageOwnerReserved3        kFlashCtrlInfoPageOwnerReserved3
#define kNvmCtrlInfoPageFactoryCerts          kFlashCtrlInfoPageFactoryCerts
#define kNvmCtrlInfoPageBootData0             kFlashCtrlInfoPageBootData0
#define kNvmCtrlInfoPageBootData1             kFlashCtrlInfoPageBootData1
#define kNvmCtrlInfoPageOwnerSlot0            kFlashCtrlInfoPageOwnerSlot0
#define kNvmCtrlInfoPageOwnerSlot1            kFlashCtrlInfoPageOwnerSlot1
#define kNvmCtrlInfoPageCreatorReserved0      kFlashCtrlInfoPageCreatorReserved0
#define kNvmCtrlInfoPageOwnerReserved4        kFlashCtrlInfoPageOwnerReserved4
#define kNvmCtrlInfoPageOwnerReserved5        kFlashCtrlInfoPageOwnerReserved5
#define kNvmCtrlInfoPageOwnerReserved6        kFlashCtrlInfoPageOwnerReserved6
#define kNvmCtrlInfoPageOwnerReserved7        kFlashCtrlInfoPageOwnerReserved7
#define kNvmCtrlInfoPageDiceCerts             kFlashCtrlInfoPageDiceCerts

// OTP field macros
#define NVM_CTRL_OTP_FIELD_SCRAMBLING FLASH_CTRL_OTP_FIELD_SCRAMBLING
#define NVM_CTRL_OTP_FIELD_ECC        FLASH_CTRL_OTP_FIELD_ECC
#define NVM_CTRL_OTP_FIELD_HE         FLASH_CTRL_OTP_FIELD_HE
#define NVM_CTRL_OTP_FIELD_HW_INFO_CFG_OVERRIDE_SCRAMBLE_DIS \
  FLASH_CTRL_OTP_FIELD_HW_INFO_CFG_OVERRIDE_SCRAMBLE_DIS
#define NVM_CTRL_OTP_FIELD_HW_INFO_CFG_OVERRIDE_ECC_DIS \
  FLASH_CTRL_OTP_FIELD_HW_INFO_CFG_OVERRIDE_ECC_DIS

// Certificate info page configuration and permissions
#define kNvmCertificateInfoPageCfg            kCertificateInfoPageCfg
#define kNvmCertificateInfoPageCreatorAccess  kCertificateInfoPageCreatorAccess
#define kNvmCertificateInfoPageOwnerAccess    kCertificateInfoPageOwnerAccess

// ---------------------------------------------------------------------------
// Functions
// ---------------------------------------------------------------------------

void nvm_ctrl_init(void);
void nvm_ctrl_disable(void);

void nvm_ctrl_status_get(nvm_ctrl_status_t *status);
void nvm_ctrl_error_code_get(nvm_ctrl_error_code_t *error_code);

OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_data_read(uint32_t addr, uint32_t word_count, void *data);

OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_info_read(const nvm_ctrl_info_page_t *info_page,
                               uint32_t offset, uint32_t word_count,
                               void *data);

OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_info_read_zeros_on_read_error(
    const nvm_ctrl_info_page_t *info_page, uint32_t offset,
    uint32_t word_count, void *data);

OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_data_write(uint32_t addr, uint32_t word_count,
                                const void *data);

OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_info_write(const nvm_ctrl_info_page_t *info_page,
                                uint32_t offset, uint32_t word_count,
                                const void *data);

OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_data_erase(uint32_t addr,
                                nvm_ctrl_erase_type_t erase_type);

OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_data_erase_verify(uint32_t addr,
                                       nvm_ctrl_erase_type_t erase_type);

OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_info_erase(const nvm_ctrl_info_page_t *info_page,
                                nvm_ctrl_erase_type_t erase_type);

void nvm_ctrl_data_default_perms_set(nvm_ctrl_perms_t perms);
void nvm_ctrl_info_perms_set(const nvm_ctrl_info_page_t *info_page,
                              nvm_ctrl_perms_t perms);

void nvm_ctrl_data_default_cfg_set(nvm_ctrl_cfg_t cfg);
nvm_ctrl_cfg_t nvm_ctrl_data_default_cfg_get(void);
nvm_ctrl_cfg_t nvm_ctrl_boot_data_cfg_get(void);

void nvm_ctrl_data_region_protect(nvm_ctrl_region_index_t region,
                                   uint32_t page_offset, uint32_t num_pages,
                                   nvm_ctrl_perms_t perms, nvm_ctrl_cfg_t cfg,
                                   hardened_bool_t lock);

void nvm_ctrl_info_cfg_set(const nvm_ctrl_info_page_t *info_page,
                            nvm_ctrl_cfg_t cfg);
void nvm_ctrl_info_cfg_lock(const nvm_ctrl_info_page_t *info_page);

void nvm_ctrl_bank_erase_perms_set(hardened_bool_t enable);
void nvm_ctrl_exec_set(uint32_t exec_val);
void nvm_ctrl_creator_info_pages_lockdown(void);

void nvm_ctrl_cert_info_page_creator_cfg(
    const nvm_ctrl_info_page_t *info_page);
void nvm_ctrl_cert_info_page_owner_restrict(
    const nvm_ctrl_info_page_t *info_page);

OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_info_type0_params_build(uint8_t bank, uint8_t page,
                                              nvm_ctrl_info_page_t *info_page);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_NVM_CTRL_H_
