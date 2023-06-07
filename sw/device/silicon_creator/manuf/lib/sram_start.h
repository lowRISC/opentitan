// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_SRAM_START_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_SRAM_START_H_

/* Values used by the start run to inform to the host about the execution.
 * The code will load SP will this value and return to the debugger using
 * ebreak.
 */
#define SRAM_MAGIC_SP_EXECUTION_DONE 0xcafebabe

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_SRAM_START_H_
