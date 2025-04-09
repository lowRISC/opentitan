// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_ISRS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_ISRS_H_

#include <stdnoreturn.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Denotes functions that have to use the interrupt handler ABI.
 *
 * These must be 4-byte aligned. Note that they don't use the `interrupt`
 * attribute since ROM_EXT handlers shut down the chip instead of returning like
 * regular handlers.
 */
#define ROM_EXT_INTERRUPT_HANDLER_ABI __attribute__((aligned(4)))

/**
 * Denotes functions that have to be near the interrupt vector, because they
 * are jumped to from it.
 */
#define ROM_EXT_VECTOR_FUNCTION __attribute__((section(".isrs")))

/**
 * ROM_EXT hardware exception handler.
 */
ROM_EXT_VECTOR_FUNCTION
ROM_EXT_INTERRUPT_HANDLER_ABI
noreturn void rom_ext_interrupt_handler(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_ISRS_H_
