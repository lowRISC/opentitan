// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_ROM_EXTS_ROM_EXT_H_
#define OPENTITAN_SW_DEVICE_ROM_EXTS_ROM_EXT_H_

#include <stdnoreturn.h>

#ifdef __cplusplus
extern "C" {
#endif

noreturn void rom_ext_boot(void);

#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_SW_DEVICE_ROM_EXTS_ROM_EXT_H_
