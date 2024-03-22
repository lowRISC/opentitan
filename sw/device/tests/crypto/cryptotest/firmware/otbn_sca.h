// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_OTBN_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_OTBN_SCA_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

status_t handle_otbn_sca_ecc256_modinv(ujson_t *uj);
status_t handle_otbn_sca_ecc256_app_select(ujson_t *uj);
status_t handle_otbn_sca_ecc256_en_masks(ujson_t *uj);
status_t handle_otbn_sca_ecc256_set_c(ujson_t *uj);
status_t handle_otbn_sca_ecc256_set_seed(ujson_t *uj);
status_t handle_otbn_sca_ecc256_ecdsa_gen_keypair(ujson_t *uj);
status_t handle_otbn_sca_ecc256_ecdsa_secret_keygen(ujson_t *uj);
status_t handle_otbn_sca_ecc256_ecdsa_keygen_fvsr_key_batch(ujson_t *uj);
status_t handle_otbn_sca_ecc256_ecdsa_keygen_fvsr_seed_batch(ujson_t *uj);
status_t handle_otbn_sca_init(ujson_t *uj);
status_t handle_otbn_sca(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_OTBN_SCA_H_
