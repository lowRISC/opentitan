// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_IBEX_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_IBEX_SCA_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

status_t handle_ibex_sca_tl_write(ujson_t *uj);
status_t handle_ibex_sca_tl_read(ujson_t *uj);
status_t handle_ibex_sca_register_file_write(ujson_t *uj);
status_t handle_ibex_sca_register_file_read(ujson_t *uj);
status_t handle_ibex_sca_init(ujson_t *uj);
status_t handle_ibex_sca(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_IBEX_SCA_H_
