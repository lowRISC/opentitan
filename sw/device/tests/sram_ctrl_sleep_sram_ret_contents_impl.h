// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_SRAM_CTRL_SLEEP_SRAM_RET_CONTENTS_IMPL_H_
#define OPENTITAN_SW_DEVICE_TESTS_SRAM_CTRL_SLEEP_SRAM_RET_CONTENTS_IMPL_H_

#include <stdbool.h>

/**
 * This test checks whether the contents of retention sram are modified
 * by either low power exit reset and hardware resets, depending on whether
 * they are rescrambed or not.
 *
 * @param scramble When true, scramble the retention sram contents.
 */
bool execute_sram_ctrl_sleep_ret_sram_contents_test(bool scramble);

#endif  // OPENTITAN_SW_DEVICE_TESTS_SRAM_CTRL_SLEEP_SRAM_RET_CONTENTS_IMPL_H_
