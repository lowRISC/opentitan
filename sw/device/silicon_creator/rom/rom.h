// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_H_

#include <stdnoreturn.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Denotes functions that have to use the interrupt handler ABI.
 *
 * These must be 4-byte aligned. Note that they don't use the `interrupt`
 * attribute since ROM handlers shut down the chip instead of returning like
 * regular handlers.
 */
#define ROM_INTERRUPT_HANDLER_ABI __attribute__((aligned(4)))

/**
 * Denotes functions that have to be near the interrupt vector, because they
 * are jumped to from it.
 */
#define ROM_VECTOR_FUNCTION __attribute__((section(".crt")))

/**
 * The first assembly procedure executed by the ROM (defined in
 * `rom.S`).
 *
 * This procedure does not obey the standard RISC-V calling convention, so it
 * must not be called from other C code.
 */
ROM_VECTOR_FUNCTION
noreturn void _rom_start_boot(void);

/**
 * The first C function executed by the ROM (defined in `rom.c`)
 */
noreturn void rom_main(void);

/**
 * ROM hardware exception handler.
 */
ROM_VECTOR_FUNCTION
ROM_INTERRUPT_HANDLER_ABI
noreturn void rom_interrupt_handler(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_H_
