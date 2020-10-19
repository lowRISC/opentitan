// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_MASK_ROM_MASK_ROM_H_
#define OPENTITAN_SW_DEVICE_MASK_ROM_MASK_ROM_H_

#include <stdnoreturn.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Denotes functions that have to use the interrupt handler ABI.
 *
 * These must be 4-byte aligned, and they use a different calling convention.
 */
#define MASK_ROM_INTERRUPT_HANDLER_ABI __attribute__((aligned(4), interrupt))

/**
 * Denotes functions that have to be near the interrupt vector, because they
 * are jumped to from it.
 */
#define MASK_ROM_VECTOR_FUNCTION __attribute__((section(".crt")))

/**
 * The first assembly procedure executed by the Mask ROM (defined in
 * `mask_rom.S`).
 *
 * This procedure does not obey the standard RISC-V calling convention, so it
 * must not be called from other C code.
 */
MASK_ROM_VECTOR_FUNCTION
void _mask_rom_start_boot(void);

/**
 * The first C function executed by the Mask ROM (defined in `mask_rom.c`)
 */
noreturn void mask_rom_boot(void);

/**
 * Mask ROM hardware exception handler.
 *
 * This may not be able to be implemented in C.
 */
MASK_ROM_VECTOR_FUNCTION
MASK_ROM_INTERRUPT_HANDLER_ABI
void mask_rom_exception_handler(void);

/**
 * Mask ROM non-maskable interrupt handler.
 *
 * This may not be able to be implemented in C.
 */
MASK_ROM_VECTOR_FUNCTION
MASK_ROM_INTERRUPT_HANDLER_ABI
void mask_rom_nmi_handler(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_MASK_ROM_MASK_ROM_H_
