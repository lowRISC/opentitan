// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_H_

#include <stdnoreturn.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * The first C function executed by the ROM (defined in `rom.c`)
 */
noreturn void rom_main(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_H_
