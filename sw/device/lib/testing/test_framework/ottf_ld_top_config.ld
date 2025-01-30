/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* TODO This configuration should be split into per-top headers */
#ifdef OPENTITAN_IS_DARJEELING
REGION_ALIAS("ottf_storage", ctn)
#else
REGION_ALIAS("ottf_storage", eflash)
#endif

#ifdef OPENTITAN_IS_ENGLISHBREAKFAST
/* Disable non-volatile scratch region and counters if building for english
 * breakfast. This should appear before the linker script. */
no_ottf_nv_scratch = 1
no_ottf_nv_counter = 1
#endif
