// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_IMM_SECTION_IMM_SECTION_EPMP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_IMM_SECTION_IMM_SECTION_EPMP_H_

#ifdef __cplusplus
extern "C" {
#endif

#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"

/**
 * Reconfigure ePMP entries to lower priority.
 *
 * ePMP will be reconfigured to:
 *    0: ROM      ----- ----
 *    1: ROM        TOR LX-R
 *    2: ROM      NAPOT L--R
 *    3: -------  ----- ----
 *    4: -------  ----- ----
 *    5: -------  ----- ----
 *    6: IM_EXT   ----- ----
 *    7: IM_EXT     TOR LX-R
 *    8:[MU_EXT   ----- ----]
 *    9:[MU_EXT     TOR LX-R]
 *   10: VIRTUAL  NAPOT L--R
 *   11: STACK      NA4 L---
 *   12: RvDM     NAPOT LXWR
 *   13: FLASH    NAPOT L--R
 *   14: MMIO     NAPOT L-WR
 *   15: RAM      NAPOT L-WR
 *
 * Mutable ROM_EXT segment (8 & 9) won't be configured by this function.
 * `imm_section_epmp_mutable_rx` will configure them when we are ready to
 * jump back to ROM.
 *
 * Entries 6~12 can be recycled in Owner SW stage.
 *
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t imm_section_epmp_reconfigure(void);

/**
 * Configure the Mutable ROM_EXT text segment with read-execute permissions.
 *
 *    8: MU_EXT   ----- ----
 *    9: MU_EXT     TOR LX-R
 *
 * Note: When address translation is enabled, the manifest argument should
 * point to the one in the virtual space.
 *
 * @param manifest Pointer to the rom_ext manifest.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t imm_section_epmp_mutable_rx(const manifest_t *manifest);

#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_IMM_SECTION_IMM_SECTION_EPMP_H_
