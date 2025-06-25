// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTOLIB_FI_ASYM_IMPL_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTOLIB_FI_ASYM_IMPL_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_fi_asym_commands.h"

/**
 * Wrapper to RSA ENC cryptolib implementation.
 *
 * @param uj_input An initialized uJSON context.
 * @param uj_output An initialized uJSON context.
 * @return OK or error.
 */
status_t cryptolib_fi_rsa_enc_impl(cryptolib_fi_asym_rsa_enc_in_t uj_input,
                                   cryptolib_fi_asym_rsa_enc_out_t *uj_output);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTOLIB_FI_ASYM_IMPL_H_
