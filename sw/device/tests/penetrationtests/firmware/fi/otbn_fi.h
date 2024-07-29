// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_OTBN_FI_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_OTBN_FI_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/ujson/ujson.h"

status_t read_otbn_err_bits(dif_otbn_err_bits_t *err_bits);

status_t handle_otbn_fi_char_hardware_dmem_op_loop(ujson_t *uj);
status_t handle_otbn_fi_char_hardware_reg_op_loop(ujson_t *uj);
status_t handle_otbn_fi_char_unrolled_dmem_op_loop(ujson_t *uj);
status_t handle_otbn_fi_char_unrolled_reg_op_loop(ujson_t *uj);
status_t handle_otbn_init_trigger(ujson_t *uj);
status_t handle_otbn_fi(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_OTBN_FI_H_
