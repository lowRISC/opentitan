// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_AES_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_AES_SCA_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * The result of an AES SCA operation.
 */
typedef enum aes_sca_error {
  /**
   * Indicates that the operation succeeded.
   */
  aesScaOk = 0,
  /**
   * Indicates some unspecified failure.
   */
  aesScaAborted = 1,
  /**
   * Indicates that the attempted operation would attempt a read/write to an
   * address that would go out of range.
   */
  aesScaOutOfRange = 2
} aes_sca_error_t;

status_t handle_aes_sca_batch_plaintext_set(ujson_t *uj);
status_t handle_aes_sca_batch_alternative_encrypt(ujson_t *uj);
status_t handle_aes_sca_seed_lfsr(ujson_t *uj);
status_t handle_aes_sca_fvsr_key_start_batch_generate(ujson_t *uj);
status_t handle_aes_sca_fvsr_key_batch_encrypt(ujson_t *uj);
status_t handle_aes_sca_fvsr_key_batch_generate(ujson_t *uj);
status_t handle_aes_sca_fvsr_key_set(ujson_t *uj);
status_t handle_aes_sca_batch_encrypt(ujson_t *uj);
status_t handle_aes_sca_single_encrypt(ujson_t *uj);
status_t handle_aes_sca_key_set(ujson_t *uj);
status_t handle_aes_sca_select_trigger_source(ujson_t *uj);
status_t handle_aes_sca_init(ujson_t *uj);
status_t handle_aes_sca(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_AES_SCA_H_
