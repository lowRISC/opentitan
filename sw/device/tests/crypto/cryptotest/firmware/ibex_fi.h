// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_IBEX_FI_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_IBEX_FI_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

status_t handle_ibex_fi_char_flash_read(ujson_t *uj);
status_t handle_ibex_fi_char_flash_write(ujson_t *uj);
status_t handle_ibex_fi_char_sram_read(ujson_t *uj);
status_t handle_ibex_fi_char_sram_write(ujson_t *uj);
status_t handle_ibex_fi_char_unconditional_branch(ujson_t *uj);
status_t handle_ibex_fi_char_conditional_branch(ujson_t *uj);
status_t handle_ibex_fi_char_mem_op_loop(ujson_t *uj);
status_t handle_ibex_fi_char_reg_op_loop(ujson_t *uj);
status_t handle_ibex_fi_char_unrolled_mem_op_loop(ujson_t *uj);
status_t handle_ibex_fi_char_unrolled_reg_op_loop(ujson_t *uj);
status_t handle_ibex_fi_init_trigger(ujson_t *uj);
status_t handle_ibex_fi_char_register_file(ujson_t *uj);
status_t handle_ibex_fi_char_register_file_read(ujson_t *uj);
status_t handle_ibex_fi(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_IBEX_FI_H_
