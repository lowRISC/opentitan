// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_AES_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_AES_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_aes_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 *
 * @file
 * @brief <a href="/hw/ip/aes/doc/">AES</a> Device Interface Functions
 *
 * This API assumes transactional nature of work, where the peripheral is
 * configured once per message (data consisting of 1..N 128-bit blocks), and
 * then "de-initialised" when this message has been fully encrypted/decrypted.
 *
 * The peripheral is configured through one of the cipher mode "start"
 * functions:
 * `dif_aes_start_ecb`, `dif_aes_start_cbc`, ... .
 *
 * Then the encryption/decryption data is fed one 128-bit block at the
 * time through `dif_aes_load_data` function. The cipher mode operation details
 * are described in the description of above mentioned "start" functions. When
 * configured in "automatic" operation mode, every "load data" call, will
 * trigger encryption/decryption. This is not true when in "manual" operation
 * mode, where encryption/decryption is triggered by explicitly setting the
 * `aes.TRIGGER.START` flag through `dif_aes_trigger` call.
 *
 * When an entire requested message has been processed the internal state of
 * AES registers must be securely cleared, by calling `dif_aes_end`.
 *
 * Please see the following documentation for further information:
 * https://docs.opentitan.org/hw/ip/aes/doc/
 * https://csrc.nist.gov/csrc/media/publications/fips/197/final/documents/fips-197.pdf
 * https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38a.pdf
 */

/**
 * A typed representation of the AES key share.
 *
 * Two part masked AES key, where XOR operation of these two parts results in
 * the actual key.
 */
typedef struct dif_aes_key_share {
  /**
   * One share of the key that when XORed with `share1` results in the actual
   * key.
   */
  uint32_t share0[8];
  /**
   * One share of the key that when XORed with `share0` results in the actual
   * key.
   */
  uint32_t share1[8];
} dif_aes_key_share_t;

/**
 * A typed representation of the AES Initialisation Vector (IV).
 */
typedef struct dif_aes_iv {
  uint32_t iv[4];
} dif_aes_iv_t;

/**
 * A typed representation of the AES data.
 */
typedef struct dif_aes_data {
  uint32_t data[4];
} dif_aes_data_t;

/**
 * AES operation.
 */
typedef enum dif_aes_operation {
  /**
   * AES encryption.
   */
  kDifAesOperationEncrypt = 1,
  /**
   * AES decryption.
   */
  kDifAesOperationDecrypt = 2,
} dif_aes_operation_t;

/**
 * AES block cipher mode of operation.
 */
typedef enum dif_aes_mode {
  /**
   * The Electronic Codebook Mode.
   * In ECB cipher mode the key must be changed for every new block of data.
   * This is the only secure way to use ECB cipher mode.
   *
   * Note: The ECB cipher mode doesn't use the iv parameter of the
   * `dif_aes_start` function.
   *
   * Note: it is discouraged to use this cipher mode, due to impractical amount
   *       of different keys required to encrypt/decrypt multi-block messages.
   */
  kDifAesModeEcb = 1,

  /**
   * The Cipher Block Chaining Mode.
   *
   * In CBC cipher mode, the same key can be used for all messages, however
   * new Initialisation Vector (IV) must be generated for any new message. The
   * following condition must be true:
   *     The IV must be unpredictable (it must not be possible to predict the IV
   *     that will be associated to the plaintext in advance of the generation
   * of the IV).
   *
   * With key length less than 256 bits, the excess portion of the `key` can be
   * written with any data (preferably random).
   */
  kDifAesModeCbc = (1 << 1),

  /**
   * The Cipher Feedback Mode.
   *
   * In CFB cipher mode, the same key can be used for all messages, however
   * new Initialisation Vector (IV) must be generated for any new message. The
   * following condition must be true:
   *     The IV must be unpredictable (it must not be possible to predict the IV
   *     that will be associated to the plaintext in advance of the generation
   * of the IV).
   *
   * With key length less than 256 bits, the excess portion of the `key` can be
   * written with any data (preferably random).
   */
  kDifAesModeCfb = (1 << 2),

  /**
   * The Output Feedback Mode.
   *
   * In OFB cipher mode, the same key can be used for all messages, and the
   * Initialization Vector (IV) need NOT be unpredictable. The following
   * conditions must be true:
   *     OFB mode requires a unique initialization vector for every message that
   *     is ever encrypted under a given key, across all messages.
   *
   * With key length less than 256 bits, the excess portion of the `key` can be
   * written with any data (preferably random).
   */
  kDifAesModeOfb = (1 << 3),

  /**
   * The Counter Mode.
   *
   * In CTR cipher mode, the same key can be used for all messages, if the
   * following condition is true:
   *     CTR mode requires a unique counter block for each plaintext block that
   *     is ever encrypted under a given key, across all messages.
   *
   * With key length less than 256 bits, the excess portion of the `key` can be
   * written with any data (preferably random).
   */
  kDifAesModeCtr = (1 << 4),
} dif_aes_mode_t;

/**
 * AES key length in bits.
 */
typedef enum dif_aes_key_length {
  /**
   * 128 bit wide AES key.
   */
  kDifAesKey128 = 1,
  /**
   * 192 bit wide AES key.
   */
  kDifAesKey192 = (1 << 1),
  /**
   * 256 bit wide AES key.
   */
  kDifAesKey256 = (1 << 2)
} dif_aes_key_length_t;

/**
 * AES manual operation.
 */
typedef enum dif_aes_manual_operation {
  /**
   * AES operates in automatic mode - which means that the encryption/decryption
   * is automatically triggered on every successful `dif_aes_*_load_data()`.
   */
  kDifAesManualOperationAuto = 0,
  /**
   * AES operates in manual mode - which means that the encryption/decryption
   * is manually triggered by `dif_aes_trigger(kDifAesTriggerStart)`.
   */
  kDifAesManualOperationManual,
} dif_aes_manual_operation_t;

/**
 * AES key sideloaded.
 *
 * Controls whether the AES uses the key provided by the key manager or
 * software.
 */
typedef enum dif_aes_key_provider {
  /**
   * The key is provided by software via `dif_aes_key_share_t`.
   */
  kDifAesKeySoftwareProvided = 0,
  /**
   * The key be provided by the key manager.
   */
  kDifAesKeySideload,
} dif_aes_key_provider_t;

/**
 * AES reseeding rate
 *
 * Controls the reseeding rate of the internal pseudo-random number generator
 * (PRNG) used for masking.
 */
typedef enum dif_aes_mask_reseeding {
  /**
   * The masking PRNG will be reseed every block.
   */
  kDifAesReseedPerBlock = 1 << 0,
  /**
   * The masking PRNG will be reseed every 64 blocks.
   */
  kDifAesReseedPer64Block = 1 << 1,
  /**
   * The masking PRNG will be reseed every 8192 blocks.
   */
  kDifAesReseedPer8kBlock = 1 << 2,
} dif_aes_mask_reseeding_t;

/**
 * Parameters for an AES transaction.
 */
typedef struct dif_aes_transaction {
  dif_aes_operation_t operation;
  dif_aes_mode_t mode;
  dif_aes_key_length_t key_len;
  dif_aes_manual_operation_t manual_operation;
  dif_aes_key_provider_t key_provider;
  dif_aes_mask_reseeding_t mask_reseeding;
  /**
   * If true the internal pseudo-random number generators used for clearing and
   * masking will be reseeded every time the key changes.
   */
  bool reseed_on_key_change;
  /**
   * If true, the internal pseudo-random number generator used for masking is
   * not advancing leading to constant masks.
   *
   * NOTE: This should only be used for development purpose (SCA), and is
   * expected to be removed for the production version.
   */
  bool force_masks;
  /**
   * If true `reseed_on_key_change` and `force_masks` will be locked until the
   * device is reset.
   */
  bool ctrl_aux_lock;
} dif_aes_transaction_t;

/**
 * Resets an instance of AES.
 *
 * Clears the internal state along with the interface registers.
 *
 * @param aes AES state data.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aes_reset(const dif_aes_t *aes);

/**
 * Begins an AES transaction in the mode selected by the `transaction->mode`.
 *
 * Each call to this function should be sequenced with a call to
 * `dif_aes_end()`.
 *
 * The peripheral must be in IDLE state for this operation to take effect, and
 * will return `kDifAesBusy` if this condition is not met.
 *
 * @param aes AES state data.
 * @param transaction Configuration data.
 * @param key Encryption/decryption key when `kDifAesKeySoftwareProvided`, can
 * be `NULL` otherwise.
 * @param iv Initialization vector when the mode isn't `kDifAesModeEcb`, can be
 * `NULL` otherwise.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aes_start(const dif_aes_t *aes,
                           const dif_aes_transaction_t *transaction,
                           const dif_aes_key_share_t *key,
                           const dif_aes_iv_t *iv);
/**
 * Ends an AES transaction.
 *
 * This function must be called at the end of every `dif_aes_<mode>_start`
 * operation.
 *
 * The peripheral must be in IDLE state for this operation to take effect, and
 * will return `kDifAesEndBusy` if this condition is not met.
 *
 * @param aes AES state data.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aes_end(const dif_aes_t *aes);

/**
 * Loads AES Input Data.
 *
 * This function will trigger encryption/decryption when configured in
 * the automatic operation mode.
 *
 * The peripheral must be able to accept the input (INPUT_READY set), and
 * will return `kDifAesLoadDataBusy` if this condition is not met.
 *
 * @param aes AES state data.
 * @param data AES Input Data.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aes_load_data(const dif_aes_t *aes, const dif_aes_data_t data);

/**
 * Reads AES Output Data.
 *
 * The peripheral must have finished previous encryption/decryption operation,
 * and have valid data in the output registers (OUTPUT_VALID set), and will
 * return `kDifAesReadOutputInvalid` if this condition is not met.
 *
 * @param aes AES state data.
 * @param data AES Output Data.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aes_read_output(const dif_aes_t *aes, dif_aes_data_t *data);

/**
 * Process a stream of data containing the plain text and outbut a stream of
 * data with the cipher text.
 *
 * This function should be used when performance is desired. It requires the
 * automatic operation mode activated.
 *
 * The peripheral must be able to accept the input (INPUT_READY set), and
 * will return `kDifAesLoadDataBusy` if this condition is not met.
 *
 * @param aes AES handle.
 * @param plain_text AES Input Data.
 * @param cipher_text AES Input Data.
 * @param block_amount The amount of blocks to be encrypted.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aes_process_data(const dif_aes_t *aes,
                                  const dif_aes_data_t *plain_text,
                                  dif_aes_data_t *cipher_text,
                                  size_t block_amount);

/**
 * AES Trigger flags.
 */
typedef enum dif_aes_trigger {
  /**
   * Trigger encrypt/decrypt.
   */
  kDifAesTriggerStart = 0,
  /**
   * Clear key, Initialisation Vector/Initial Counter Value and input data.
   */
  kDifAesTriggerKeyIvDataInClear,
  /**
   * Clear Output Data registers.
   */
  kDifAesTriggerDataOutClear,
  /**
   * Perform reseed of the internal state.
   */
  kDifAesTriggerPrngReseed,
} dif_aes_trigger_t;

/**
 * Triggers one of `dif_aes_trigger_t` operations.
 *
 * All the triggers are applicable to both (automatic and manual) modes, with
 * the exception of `kDifAesTriggerStart`, which is ignored in automatic mode.
 *
 * @param aes AES state data.
 * @param trigger AES trigger.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aes_trigger(const dif_aes_t *aes, dif_aes_trigger_t trigger);

/**
 * AES Status flags.
 */
typedef enum dif_aes_status {
  /**
   * Device is idle.
   */
  kDifAesStatusIdle = 0,
  /**
   * Device has stalled (only relevant in automatic
   * operation mode). Output data overwrite
   * protection.
   */
  kDifAesStatusStall,
  /**
   * Output data has been overwritten by the AES unit before the processor
   * could fully read it. This bit is "sticky" for the entire duration of
   * the current transaction.
   */
  kDifAesStatusOutputLost,
  /**
   * Device output is valid/ready. Denotes a
   * successful encrypt or decrypt operation.
   */
  kDifAesStatusOutputValid,
  /**
   * Device Input Data registers can be written to
   * (ready to accept new input data).
   */
  kDifAesStatusInputReady,
  /**
   * Fatal alert conditions include i) storage errors in the Control Register,
   * and ii) if any internal FSM enters an invalid state.
   */
  kDifAesStatusAlertFatalFault,
  /**
   * Recoverable alert conditions include update errors in the Control Register.
   */
  kDifAesStatusAlertRecovCtrlUpdateErr,
} dif_aes_status_t;

/**
 * Queries the AES status flags.
 *
 * @param aes AES state data.
 * @param flag Status flag to query.
 * @param[out] set Flag state (set/unset).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aes_get_status(const dif_aes_t *aes, dif_aes_status_t flag,
                                bool *set);

/**
 * Read the current initialization vector from its register.
 *
 * @param aes AES handle.
 * @param iv The pointer to receive the initialization vector.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aes_read_iv(const dif_aes_t *aes, dif_aes_iv_t *iv);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_AES_H_
