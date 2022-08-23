// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_OWNER_BARE_METAL_BARE_METAL_H_
#define OPENTITAN_SW_DEVICE_SILICON_OWNER_BARE_METAL_BARE_METAL_H_

#include <stdnoreturn.h>

#ifdef __cplusplus
extern "C" {
#endif

noreturn void bare_metal_main(void);

#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_OWNER_BARE_METAL_BARE_METAL_H_
