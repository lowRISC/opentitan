// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_AES_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_AES_H_

/**
 * @file
 * @brief <a href="/hw/ip/aes/doc/">AES</a> Device Interface Functions
 */

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_warn_unused_result.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
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
 * AES key length in bits.
 */
typedef enum dif_aes_key_length {
  /**
   * 128 bit wide AES key.
   */
  kDifAesKey128 = 0,
  /**
   * 192 bit wide AES key.
   */
  kDifAesKey192,
  /**
   * 256 bit wide AES key.
   */
  kDifAesKey256,
} dif_aes_key_length_t;

/**
 * AES mode.
 */
typedef enum dif_aes_mode {
  /**
   * AES encryption mode.
   */
  kDifAesModeEncrypt = 0,
  /**
   * AES decryption mode.
   */
  kDifAesModeDecrypt,
} dif_aes_mode_t;

/**
 * AES operation.
 */
typedef enum dif_aes_operation {
  /**
   * AES operates in automatic mode - which means that the encryption/decryption
   * is automatically triggered on every successful `dif_aes_*_load_data()`.
   */
  kDifAesOperationAuto = 0,
  /**
   * AES operates in manual mode - which means that the encryption/decryption
   * is manually triggered by `dif_aes_trigger(kDifAesTriggerStart)`.
   */
  kDifAesOperationManual,
} dif_aes_operation_t;

/**
 * AES masking.
 *
 * NOTE:
 * This should only be used for development purpose (SCA), and expected to be
 * removed before the production version.
 */
typedef enum dif_aes_masking {
  /**
   * Pseudo-random generator is used for masking.
   */
  kDifAesMaskingInternalPrng = 0,
  /**
   * Completely disables masking by forcing all masks to zero.
   */
  kDifAesMaskingForceZero,
} dif_aes_masking_t;

/**
 * Parameters for an AES transaction.
 */
typedef struct dif_aes_transaction {
  dif_aes_key_length_t key_len;
  dif_aes_mode_t mode;
  dif_aes_operation_t operation;
  dif_aes_masking_t masking;
} dif_aes_transaction_t;

/**
 * An AES alert type.
 */
typedef enum dif_aes_alert {
  /**
   * Fatal alert conditions include i) storage errors in the Control Register,
   * and ii) if any internal FSM enters an invalid state.
   */
  kDifAlertFatalFault = 0,
  /**
   * Recoverable alert conditions include update errors in the Control Register.
   */
  kDifAlertRecovCtrlUpdateErr,
} dif_aes_alert_t;

/**
 * Hardware instantiation parameters for AES.
 *
 * This struct describes information about the underlying hardware that is
 * not determined until the hardware design is used as part of a top-level
 * design.
 */
typedef struct dif_aes_params {
  /**
   * The base address for the AES hardware registers.
   */
  mmio_region_t base_addr;
} dif_aes_params_t;

/**
 * A handle to AES.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_aes {
  dif_aes_params_t params;
} dif_aes_t;

/**
 * The result of a AES operation.
 */
typedef enum dif_aes_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifAesOk = 0,
  /**
   * Indicates some unspecified failure.
   */
  kDifAesError = 1,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifAesBadArg = 2,
} dif_aes_result_t;

/**
 * Creates a new handle for AES.
 *
 * This function does not actuate the hardware.
 *
 * @param params Hardware instantiation parameters.
 * @param[out] aes Out param for the initialised handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aes_result_t dif_aes_init(dif_aes_params_t params, dif_aes_t *aes);

/**
 * The result of a AES reset operation.
 */
typedef enum dif_aes_reset_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifAesResetOk = kDifAesOk,
  /**
   * Indicates some unspecified failure.
   */
  kDifAesResetError = kDifAesError,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifAesResetBadArg = kDifAesBadArg,
  /**
   * Device is busy, and cannot perform the requested operation.
   */
  kDifAesResetBusy,
} dif_aes_reset_result_t;

/**
 * Resets an instance of AES.
 *
 * Clears the internal state along with the interface registers.
 *
 * @param aes AES state data.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aes_reset_result_t dif_aes_reset(const dif_aes_t *aes);

/**
 * The result of a AES start operation.
 */
typedef enum dif_aes_start_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifAesStartOk = kDifAesOk,
  /**
   * Indicates some unspecified failure.
   */
  kDifAesStartError = kDifAesError,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifAesStartBadArg = kDifAesBadArg,
  /**
   * Device is busy, and cannot perform the requested operation.
   */
  kDifAesStartBusy,
} dif_aes_start_result_t;

/**
 * Begins an AES transaction in ECB mode.
 *
 * In ECB cipher mode the key must be changed for every new block of data. This
 * is the only secure way to use ECB cipher mode.
 *
 * Each call to this function should be sequenced with a call to
 * `dif_aes_end()`.
 *
 * Note: it is discouraged to use this cipher mode, due to inpractical amount
 *       of different keys required to encrypt/decrypt multi-block messages.
 *
 * The peripheral must be in IDLE state for this operation to take
 * effect, and will return `kDifAesStartBusy` if this condition is not
 * met.
 *
 * @param aes AES state data.
 * @param transaction Configuration data.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aes_start_result_t dif_aes_start_ecb(
    const dif_aes_t *aes, const dif_aes_transaction_t *transaction,
    dif_aes_key_share_t key);

/**
 * Begins an AES transaction in CBC mode.
 *
 * In CBC cipher mode, the same key can be used for all messages, however
 * new Initialisation Vector (IV) must be generated for any new message. The
 * following condition must be true:
 *     The IV must be unpredictable (it must not be possible to predict the IV
 *     that will be associated to the plaintext in advance of the generation of
 *     the IV).
 *
 * With key length less than 256 bits, the excess portion of the `key` can be
 * written with any data (preferably random).
 *
 * The peripheral must be in IDLE state for this operation to take effect, and
 * will return `kDifAesStartBusy` if this condition is not met.
 *
 * @param aes AES state data.
 * @param transaction Configuration data.
 * @param key_share Masked AES key.
 * @param iv AES Initialisation Vector.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aes_start_result_t dif_aes_start_cbc(
    const dif_aes_t *aes, const dif_aes_transaction_t *transaction,
    dif_aes_key_share_t key, dif_aes_iv_t iv);

/**
 * Begins an AES transaction in CTR mode.
 *
 * In CTR cipher mode, the same key can be used for all messages, if the
 * following condition is true:
 *     CTR mode requires a unique counter block for each plaintext block that
 *     is ever encrypted under a given key, across all messages.
 *
 * With key length less than 256 bits, the excess portion of the `key` can be
 * written with any data (preferably random).
 *
 * The peripheral must be in IDLE state for this operation to take effect, and
 * will return `kDifAesStartBusy` if this condition is not met.
 *
 * @param aes AES state data.
 * @param transaction Configuration data.
 * @paran key Masked AES key.
 * @param iv AES Initial Counter Value.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aes_start_result_t dif_aes_start_ctr(
    const dif_aes_t *aes, const dif_aes_transaction_t *transaction,
    dif_aes_key_share_t key, dif_aes_iv_t iv);

/**
 * The result of an AES end operation.
 */
typedef enum dif_aes_end_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifAesEndOk = kDifAesOk,
  /**
   * Indicates some unspecified failure.
   */
  kDifAesEndError = kDifAesError,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifAesEndBadArg = kDifAesBadArg,
  /**
   * Device is busy, and cannot perform the requested operation.
   */
  kDifAesEndBusy,
} dif_aes_end_result_t;

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
DIF_WARN_UNUSED_RESULT
dif_aes_end_result_t dif_aes_end(const dif_aes_t *aes);

/**
 * The result of an AES load data operation.
 */
typedef enum dif_aes_load_data_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifAesLoadDataOk = kDifAesOk,
  /**
   * Indicates some unspecified failure.
   */
  kDifAesLoadDataError = kDifAesError,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifAesLoadDataBadArg = kDifAesBadArg,
  /**
   * Device is busy, and cannot perform the requested operation.
   */
  kDifAesLoadDataBusy,
} dif_aes_load_data_result_t;

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
DIF_WARN_UNUSED_RESULT
dif_aes_load_data_result_t dif_aes_load_data(const dif_aes_t *aes,
                                             const dif_aes_data_t data);

/**
 * The result of an AES data read operation.
 */
typedef enum dif_aes_read_data_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifAesReadOutputOk = kDifAesOk,
  /**
   * Indicates some unspecified failure.
   */
  kDifAesReadOutputError = kDifAesError,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifAesReadOutputBadArg = kDifAesBadArg,
  /**
   * The AES unit has no valid output.
   */
  kDifAesReadOutputInvalid,
} dif_aes_read_output_result_t;

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
DIF_WARN_UNUSED_RESULT
dif_aes_read_output_result_t dif_aes_read_output(const dif_aes_t *aes,
                                                 dif_aes_data_t *data);

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
DIF_WARN_UNUSED_RESULT
dif_aes_result_t dif_aes_trigger(const dif_aes_t *aes,
                                 dif_aes_trigger_t trigger);

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
 * @param set Flag state (set/unset).
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aes_result_t dif_aes_get_status(const dif_aes_t *aes, dif_aes_status_t flag,
                                    bool *set);

/**
 * Forces a particular alert, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param aes AES state data.
 * @param alert An alert type.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aes_result_t dif_aes_alert_force(const dif_aes_t *aes,
                                     dif_aes_alert_t alert);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_AES_H_
