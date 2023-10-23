// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_LIB_SW_DEVICE_SILICON_CREATOR_ROM_PATCH_H_
#define OPENTITAN_SW_LIB_SW_DEVICE_SILICON_CREATOR_ROM_PATCH_H_

#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/base/multibits.h"
#include "sw/lib/sw/device/silicon_creator/error.h"
#include "sw/lib/sw/device/silicon_creator/sigverify/sigverify.h"

#include "rv_core_ibex_regs.h"

/**
 * @file
 * @brief Second Stage ROM patching library.
 */

/**
 * A ROM patch address matching table entry.
 */
typedef struct rom_patch_match_regs {
  uint32_t m_base;  // Matching address
  uint32_t r_base;  // Remapped address
} rom_patch_match_regs_t;

/**
 * A ROM patch structure.
 *
 * The patch signature is located after the patch code section.
 */
typedef struct rom_patch {
  /**
   * ROM patch header:
   *
   * - Bits 0-3: Lock Valid multi-bit boolean value (MuBi)
   * - Bits 4-7: Program Start multi-bit boolean value (MuBi)
   * - Bits 8-23: Total size of the patch in DWORDS, including the patch
                  header, patch table, patch body and the digital signature.
   * - Bits 24-31: Patch revision
   */
  uint32_t header;

  /**
   * The address matching table.
   */
  rom_patch_match_regs_t table[RV_CORE_IBEX_PARAM_NUM_REGIONS];

  /**
   * The actual patch code.
   */
  uint32_t patch[];
} rom_patch_t;

OT_ASSERT_MEMBER_OFFSET(rom_patch_t, header, 0);
OT_ASSERT_MEMBER_OFFSET(rom_patch_t, table, 4);
OT_ASSERT_MEMBER_OFFSET(rom_patch_t, patch, 260);

enum {
  /* Invalid ROM patch address */
  kRomPatchInvalidAddr = UINTPTR_MAX,
};

/**
 * Finds the latest ROM patch to be applied.
 * The latest patch is the highest revision, valid patch from the OTP ROM_PATCH
 * partition.
 *
 * @param before_patch_addr When this parameter is different than
 *        kRomPatchInvalidAddr, the returned patch is the one with the highest
 *        revision that is equal or lower than before_patch_addr revision, i.e.
 *        the latest before before_patch_addr.
 *        When this parameter is set to kRomPatchInvalidAddr, the function
 *        looks for the absolute highest patch revision number.
 *
 * @return Address of the latest ROM patch or kRomPatchInvalidAddr if no patch
 *         could be found or for errors.
 */
OT_WARN_UNUSED_RESULT uintptr_t rom_patch_latest(uintptr_t before_patch_addr);

/**
 * Applies a ROM patch into SRAM and enables the corresponding Ibex wrapper
 * address remappings.
 *
 * @param patch_addr Address of the ROM patch to apply.
 * @param patch_digest Input address for the ROM patch digest. This function
 *        computes a SHA256 digest of the applied ROM patch and stores it at
 *        this address.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t rom_patch_apply(const uintptr_t patch_addr,
                            hmac_digest_t *const patch_digest);

/**
 * Checks that a patch is valid.
 * A valid patch lives withing the OTP ROM patch region and has a non-zero size.
 *
 * @param patch_addr Address of the ROM patch to check.
 * @return True if the patch is valid, false otherwise.
 */
OT_WARN_UNUSED_RESULT bool rom_patch_valid(const uintptr_t patch_addr);

#endif  // OPENTITAN_SW_LIB_SW_DEVICE_SILICON_CREATOR_ROM_PATCH_H_
