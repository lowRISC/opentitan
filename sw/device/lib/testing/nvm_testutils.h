// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_NVM_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_NVM_TESTUTILS_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/silicon_creator/lib/nvm_ctrl.h"

// nvm_page_perms_t, nvm_page_cfg_t, and nvm_info_page_t are defined in
// nvm_ctrl.h (included
// above).  The semantics for nvm_testutils functions are:
//   - nvm_testutils_info_page_setup: `true` enables, `false` disables.
//   - nvm_testutils_info_page_set:   `true` enables, `false` leaves unchanged.
//   - nvm_testutils_info_page_clear: `true` disables, `false` leaves unchanged.

/** Read-only: read selected, write and erase not selected. */
extern const nvm_page_perms_t kPageReadOnly;
/** Read-write: read, write, and erase all selected. */
extern const nvm_page_perms_t kPageReadWrite;
/** Write-only: read not selected, write and erase selected. */
extern const nvm_page_perms_t kPageWriteOnly;

/** Scrambled: scrambling and ECC selected, high-endurance not selected. */
extern const nvm_page_cfg_t kPageScrambleCfg;
/** Plain: scrambling not selected, ECC selected, high-endurance not selected.
 */
extern const nvm_page_cfg_t kPagePlainCfg;
/** Raw: scrambling not selected, ECC not selected, high-endurance not selected.
 * Use for pages written without ECC encoding (e.g. AST calibration data).
 */
extern const nvm_page_cfg_t kPageRawCfg;

/**
 * Wait for the flash controller to finish its initialization sequence.
 *
 * Must be called before any flash operations when running from SRAM (e.g. in
 * SRAM provisioning programs) to ensure the controller is ready.
 *
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_wait_for_init(void);

/**
 * Set all access permissions and configuration flags for an NVM info page.
 *
 * Writes all fields unconditionally: `true` → enabled, `false` → disabled.
 *
 * @param page  Logical info page identifier.
 * @param perms Permission values to apply to all fields.
 * @param cfg   Configuration values to apply to all fields.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_info_page_setup(nvm_info_page_t page,
                                       nvm_page_perms_t perms,
                                       nvm_page_cfg_t cfg);

/**
 * Enable selected permission and configuration bits, leaving others unchanged.
 *
 * For each field set to `true` in `perms`/`cfg`, the corresponding bit is
 * enabled (kMultiBitBool4True).  Fields set to `false` are not modified.
 *
 * @param page  Logical info page identifier.
 * @param perms Bitmask of permissions to enable.
 * @param cfg   Bitmask of configuration bits to enable.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_info_page_set(nvm_info_page_t page,
                                     nvm_page_perms_t perms,
                                     nvm_page_cfg_t cfg);

/**
 * Disable selected permission and configuration bits, leaving others unchanged.
 *
 * For each field set to `true` in `perms`/`cfg`, the corresponding bit is
 * disabled (kMultiBitBool4False).  Fields set to `false` are not modified.
 *
 * @param page  Logical info page identifier.
 * @param perms Bitmask of permissions to disable.
 * @param cfg   Bitmask of configuration bits to disable.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_info_page_clear(nvm_info_page_t page,
                                       nvm_page_perms_t perms,
                                       nvm_page_cfg_t cfg);

/**
 * Write data to a logical NVM info page.
 *
 * The caller must call nvm_testutils_info_page_setup() before this function to
 * configure the region properties (scrambling, ECC, permissions).
 *
 * When `erase_before_write` is true the page is erased first and a readback
 * is performed to verify the write.
 *
 * @param page               Logical info page identifier.
 * @param byte_offset        Byte offset from the start of the page.
 * @param data               Data words to write.
 * @param word_count         Number of 32-bit words to write (max 64).
 * @param erase_before_write Erase the page before writing.
 * @param readback           Read back and verify data after writing.
 *                           Set false for pages not readable in the current LC
 *                           state (e.g. WaferAuthSecret in TEST_UNLOCKED).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_write_info_page(nvm_info_page_t page,
                                       uint32_t byte_offset,
                                       const uint32_t *data, size_t word_count,
                                       bool erase_before_write, bool readback);

/**
 * Read data from a logical NVM info page.
 *
 * The caller must call nvm_testutils_info_page_setup() before this function to
 * configure the region properties (scrambling, ECC, permissions).
 *
 * @param page         Logical info page identifier.
 * @param byte_offset  Byte offset from the start of the page.
 * @param[out] data    Output buffer for the read data.
 * @param word_count   Number of 32-bit words to read.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_read_info_page(nvm_info_page_t page,
                                      uint32_t byte_offset, uint32_t *data,
                                      size_t word_count);

/**
 * Initialize the NVM controller at ROM/boot time.
 *
 * Starts the flash controller, waits for initialization to complete,
 * optionally applies default region properties read from OTP, and enables
 * flash access and instruction fetch.  Call this once from test ROM before any
 * other NVM operation.
 *
 * @param otp_flash_default_cfg CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG OTP word;
 *   pass 0 when HAS_OTP_CTRL is not available or the field reads as zero.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_rom_init(uint32_t otp_flash_default_cfg);

/**
 * Lock the region configuration for an NVM info page.
 *
 * Once locked the region properties cannot be changed until the device is
 * reset. Passing `lock = false` is a no-op and always returns OK_STATUS.
 *
 * @param page Logical info page identifier.
 * @param lock If true, lock the region configuration; if false, do nothing.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_info_page_lock(nvm_info_page_t page, bool lock);

/**
 * Set properties for an NVM data region and enable it.
 *
 * Configures the base page, size, access permissions, and memory properties
 * for a data region, then enables it.  Writes all fields unconditionally.
 *
 * @param region Data region index.
 * @param base   Base page index of the region.
 * @param size   Size of the region in pages.
 * @param perms  Permission values to apply (read, write, erase).
 * @param cfg    Configuration values to apply (scrambling, ECC, HE).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_data_region_setup(uint32_t region, uint32_t base,
                                         uint32_t size, nvm_page_perms_t perms,
                                         nvm_page_cfg_t cfg);

/**
 * Lock the region configuration for an NVM data region.
 *
 * Once locked the region properties cannot be changed until the device is
 * reset. Passing `lock = false` is a no-op and always returns OK_STATUS.
 *
 * @param region Data region index.
 * @param lock   If true, lock the region configuration; if false, do nothing.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_data_region_lock(uint32_t region, bool lock);

/**
 * Log any outstanding flash controller fault status registers.
 *
 * Initialises the NVM controller internally, reads the fault status registers
 * via flash_ctrl_testutils_show_faults, and logs any faults.  Useful at the
 * start of a test to confirm the controller is in a clean state.
 *
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_show_faults(void);

/**
 * Set the NVM controller default data region properties.
 *
 * Writes all fields of the default region unconditionally using the same
 * bool-to-MultiBitBool4 semantics as nvm_testutils_info_page_setup.
 * Hardware register state persists, so subsequent NVM operations will observe
 * these settings.
 *
 * @param perms Permission values to apply (read, write, erase).
 * @param cfg   Configuration values to apply (scrambling, ECC, HE).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_default_region_setup(nvm_page_perms_t perms,
                                            nvm_page_cfg_t cfg);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_NVM_TESTUTILS_H_
