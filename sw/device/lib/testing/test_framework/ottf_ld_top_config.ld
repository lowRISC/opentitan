/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* TODO This configuration should be split into per-top headers */
#ifdef OPENTITAN_IS_DARJEELING
MEMORY {
    /* There is a 1MiB RAM within the CTN at offset 16MiB to hold the
     * firmware under test in DV. */
    ctn_ram(rwx) : ORIGIN = ORIGIN(ctn) + 0x1000000, LENGTH = 0x100000
}
REGION_ALIAS("ottf_storage", ctn_ram)

/* Darjeeling has no flash_ctrl/rram_ctrl, so no NVM slot tail to reserve. */
_nvm_slot_reserved_bytes = 0;
#else
REGION_ALIAS("ottf_storage", nvm)
#endif

#ifdef OPENTITAN_IS_ENGLISHBREAKFAST
/* Disable non-volatile scratch region and counters if building for english
 * breakfast. This should appear before the linker script. */
no_ottf_nv_scratch = 1
no_ottf_nv_counter = 1
#endif
