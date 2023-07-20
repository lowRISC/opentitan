// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_KMAC_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_KMAC_H_

/**
 * @file
 * @brief <a href="/hw/ip/kmac/doc/">KMAC</a> Device Interface Functions
 */

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_kmac_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * This API implements an interface for the KMAC hardware.
 *
 * The KMAC hardware implements the following cryptographic hash and message
 * authentication code (MAC) functions:
 *
 * - SHA-3 [1]
 * - SHAKE [1]
 * - cSHAKE [2]
 * - KMAC [2]
 *
 * The following sequence of operations is required to initialize the KMAC
 * hardware:
 *
 * - `dif_kmac_init()`
 * - `dif_kmac_configure()`
 *
 * If configuration changes are required then `dif_kmac_configure` can be called
 * again so long as there are no operations in progress.
 *
 * The following sequence of operations is required to execute an operation:
 *
 * - `dif_kmac_{sha3,shake,cshake,kmac}_start()`
 * - `dif_kmac_absorb()`
 * - `dif_kmac_squeeze()`
 * - `dif_kmac_end()`
 *
 * This is a streaming API and the `dif_kmac_absorb` and `dif_kmac_squeeze`
 * functions may be called multiple times during a single operation. Once
 * `dif_kmac_squeeze` has been called however no further `dif_kmac_absorb` calls
 * may be made. See NIST FIPS 202 [1] for more information about the sponge
 * construction and the 'absorbing' and 'squeezing' states.
 *
 * Please see the following documentation for more information about the KMAC
 * hardware:
 * https://docs.opentitan.org/hw/ip/kmac/doc/
 *
 * References:
 * [1] - NIST FIPS 202
 *       SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions
 *       http://dx.doi.org/10.6028/NIST.FIPS.202
 * [2] - NIST Special Publication 800-185
 *       SHA-3 Derived Functions: cSHAKE, KMAC, TupleHash and ParallelHash
 *       https://doi.org/10.6028/NIST.SP.800-185
 */

/**
 * Supported entropy modes.
 *
 * Entropy may be provided by the entropy distribution network (EDN) or using a
 * seed provided by software.
 */
typedef enum dif_kmac_entropy_mode {
  kDifKmacEntropyModeIdle = 0,
  kDifKmacEntropyModeEdn,
  kDifKmacEntropyModeSoftware,
} dif_kmac_entropy_mode_t;

/**
 * Maximum lengths supported by the KMAC unit.
 */
enum {

  /**
   * The maximum length in bytes of a customization string (S) before it has
   * been encoded.
   */
  kDifKmacMaxCustomizationStringLen = 32,

  /**
   * The maximum number of bytes required to encode the length of the
   * customization string.
   *
   * Assumes maximum customization string length of 32 bytes (256 bits).
   */
  kDifKmacMaxCustomizationStringOverhead = 3,

  /**
   * The maximum length in bytes of a function name (N) before it has been
   * encoded.
   */
  kDifKmacMaxFunctionNameLen = 4,

  /**
   * The maximum number of bytes required to encode the length of the function
   * name.
   *
   * Assumes maximum function name length of 4 bytes (32 bits).
   */
  kDifKmacMaxFunctionNameOverhead = 2,

  /**
   * The maximum output length (L) that can be set when starting a KMAC
   * operation.
   *
   * The length is in 32-bit words and is designed to be low enough that the
   * length in bits can still be represented by an unsigned 32-bit integer.
   */
  kDifKmacMaxOutputLenWords = (UINT32_MAX - 32) / 32,

  /**
   * The maximum key length supported by the KMAC operation.
   *
   * The length is in 32-bit words.
   */
  kDifKmacMaxKeyLenWords = 512 / 32,

  /**
   * The length of the software entropy seed.
   *
   * The length is in 32-bit words.
   */
  kDifKmacEntropySeedWords = 5,
  /**
   * The offset of the second share within the output state register.
   */
  kDifKmacStateShareOffset = 0x100,
};

/**
 * Runtime configuration for KMAC.
 *
 * This struct describes runtime information for configuration of the hardware.
 */
typedef struct dif_kmac_config {
  /**
   * Entropy mode specifying the source of entropy (EDN or software).
   */
  dif_kmac_entropy_mode_t entropy_mode;

  /**
   * Entropy fast process mode when enabled prevents the KMAC unit consuming
   * entropy unless it is processing a secret key. This process should not be
   * used when resistance against side-channel attacks is required, because
   * it may lead to leakage of the secret key in the power trace.
   */
  bool entropy_fast_process;

  /**
   * Entropy seed. Only used when the source of entropy is software.
   */
  uint32_t entropy_seed[kDifKmacEntropySeedWords];

  /**
   * The number of KMAC invocations that triggers an automatic seed request from
   * EDN.
   */
  uint16_t entropy_hash_threshold;

  /**
   * Number of clock cycles to wait for the EDN to reseed the entropy generator
   * before an error is raised (see `dif_kmac_get_error`). If 0 the unit will
   * wait forever.
   */
  uint16_t entropy_wait_timer;

  /**
   * Prescaler value that determines how many clock pulse triggers an increment
   * in the timer counter.
   */
  uint16_t entropy_prescaler;

  /**
   * Convert the message to big-endian byte order.
   * Note: this option currently had no effect since the message is sent a byte
   * at a time but will in the future.
   */
  bool message_big_endian;

  /**
   * Convert the output state (digest) to big-endian byte order on a word
   * granularity.
   */
  bool output_big_endian;

  /**
   * Place kmac inside key sideload mode
   */
  bool sideload;

  /**
   * Message Masking with PRNG.
   * If true, KMAC applies PRNG to the input messages to the Keccak module when
   * KMAC mode is on.
   */
  bool msg_mask;

} dif_kmac_config_t;

/**
 * A KMAC operation state context.
 */
typedef struct dif_kmac_operation_state {
  /**
   * Whether the 'squeezing' phase has been started.
   */
  bool squeezing;

  /**
   * Flag indicating whether the output length (d) should be right encoded in
   * software and appended to the end of the message. The output length is
   * required to be appended to the message as part of a KMAC operation.
   */
  bool append_d;

  /**
   * Offset into the output state.
   */
  size_t offset;

  /**
   * The rate (r) in 32-bit words.
   */
  size_t r;

  /**
   * The output length (d) in 32-bit words.
   *
   * If the output length is not fixed then this field will be set to 0.
   *
   * Note: if the output length is fixed length will be modified to ensure that
   * `d - offset` always accurately reflects the number of words remaining.
   */
  size_t d;
} dif_kmac_operation_state_t;

/**
 * Supported SHA-3 modes of operation.
 */
typedef enum dif_kmac_mode_sha3 {
  /** SHA-3 with 224 bit strength. */
  kDifKmacModeSha3Len224,
  /** SHA-3 with 256 bit strength. */
  kDifKmacModeSha3Len256,
  /** SHA-3 with 384 bit strength. */
  kDifKmacModeSha3Len384,
  /** SHA-3 with 512 bit strength. */
  kDifKmacModeSha3Len512,
} dif_kmac_mode_sha3_t;

/**
 * Supported SHAKE modes of operation.
 */
typedef enum dif_kmac_mode_shake {
  /** SHAKE with 128 bit strength. */
  kDifKmacModeShakeLen128,
  /** SHAKE with 256 bit strength. */
  kDifKmacModeShakeLen256,
} dif_kmac_mode_shake_t;

/**
 * Supported cSHAKE modes of operation.
 */
typedef enum dif_kmac_mode_cshake {
  /** cSHAKE with 128 bit strength. */
  kDifKmacModeCshakeLen128,
  /** cSHAKE with 256 bit strength. */
  kDifKmacModeCshakeLen256,
} dif_kmac_mode_cshake_t;

/**
 * Supported KMAC modes of operation.
 */
typedef enum dif_kmac_mode_kmac {
  /** KMAC with 128 bit strength. */
  kDifKmacModeKmacLen128,
  /** KMAC with 256 bit strength. */
  kDifKmacModeKmacLen256,
} dif_kmac_mode_kmac_t;

/**
 * Key length.
 *
 * The key length is specified in bits.
 */
typedef enum dif_kmac_key_length {
  /** Software provided 128 bit key. */
  kDifKmacKeyLen128 = 0,
  /** Software provided 192 bit key. */
  kDifKmacKeyLen192 = 1,
  /** Software provided 256 bit key. */
  kDifKmacKeyLen256 = 2,
  /** Software provided 384 bit key. */
  kDifKmacKeyLen384 = 3,
  /** Software provided 512 bit key. */
  kDifKmacKeyLen512 = 4,
} dif_kmac_key_length_t;

/**
 * A key for KMAC operations.
 *
 * The key is provided in two parts, `share0` and `share1`. These are
 * combined using a bitwise XOR operation in the KMAC unit to produce the real
 * key.
 *
 * The key shares are encoded in little endian byte order. This is fixed and
 * cannot be changed (unlike the byte order used for the message and state).
 *
 * Unused words in the key shares must be set to 0.
 */
typedef struct dif_kmac_key {
  uint32_t share0[kDifKmacMaxKeyLenWords];
  uint32_t share1[kDifKmacMaxKeyLenWords];
  dif_kmac_key_length_t length;
} dif_kmac_key_t;

/**
 * An encoded bit string used for customization string (S).
 *
 * Use `dif_kmac_customization_string_init` to initialize.
 */
typedef struct dif_kmac_customization_string {
  /** Encoded S: left_encode(len(S)) || S */
  char buffer[kDifKmacMaxCustomizationStringLen +
              kDifKmacMaxCustomizationStringOverhead];
  /** Length of data in buffer in bytes. */
  uint32_t length;
} dif_kmac_customization_string_t;

/**
 * An encoded bit string used for function name (N).
 *
 * Use `dif_kmac_function_name_init` to initialize.
 */
typedef struct dif_kmac_function_name {
  /** Encoded N: left_encode(len(N)) || N */
  char buffer[kDifKmacMaxFunctionNameLen + kDifKmacMaxFunctionNameOverhead];
  /** Length of data in buffer in bytes. */
  uint32_t length;
} dif_kmac_function_name_t;

/**
 * Error reported by KMAC unit.
 *
 * Codes taken from hw/ip/kmac/rtl/kmac_pkg.sv:err_code_e
 */
typedef enum dif_kmac_error {
  /**
   * No error has occured.
   */
  kDifErrorNone,

  /**
   * The Key Manager has raised an error because the secret key is not valid.
   */
  kDifErrorKeyNotValid,

  /**
   * An attempt was made to write data into the message FIFO but the KMAC unit
   * was not in the correct state to receive the data.
   */
  kDifErrorSoftwarePushedMessageFifo,

  /**
   * An invalid state transition was attempted (e.g. idle -> run without
   * intermediate process state).
   */
  kDifErrorSoftwarePushedWrongCommand,

  /**
   * The entropy wait timer has expired.
   */
  kDifErrorEntropyWaitTimerExpired = 0x04000000,

  /**
   * Incorrect entropy mode when entropy is ready.
   */
  kDifErrorEntropyModeIncorrect,

  /**
   * An error was encountered but the cause is unknown.
   */
  kDifErrorUnknownError,
} dif_kmac_error_t;

/**
 * The state of the message FIFO used to buffer absorbed data.
 *
 * The hardware defined these status in different bit fields, however they work
 * better in the same field. i.e the fifo can't be empty and full at the same
 * time. That said, the values chosen for this enum allow the conversion from
 * the register bits to this enum without branches.
 */
typedef enum dif_kmac_fifo_state {
  /** The message FIFO is not empty or full. */
  kDifKmacFifoStatePartial = 0,
  /** The message FIFO is empty. */
  kDifKmacFifoStateEmpty = 1 << 0,
  /** The message FIFO is full. Further writes will block. */
  kDifKmacFifoStateFull = 1 << 1,
} dif_kmac_fifo_state_t;

typedef enum dif_kmac_sha3_state {
  /**
   * SHA3 hashing engine is in idle state.
   */
  kDifKmacSha3StateIdle = 1 << 0,

  /**
   * SHA3 is receiving message stream and processing it.
   */
  kDifKmacSha3StateAbsorbing = 1 << 1,

  /**
   * SHA3 completes sponge absorbing stage. In this stage, SW can manually run
   * the hashing engine.
   */
  kDifKmacSha3StateSqueezing = 1 << 2,
} dif_kmac_sha3_state_t;

/**
 * The kmac error faults.
 *
 * The hardware defined these status in different bit fields, however they work
 * better in the same field. Then the values chosen for this enum allow the
 * conversion from the register bits to this enum without branches.
 */
typedef enum dif_kmac_alert_faults {
  /**
   * Neither errors nor fault has occurred.
   */
  kDifKmacAlertNone = 0,
  /**
   * A fatal fault has occurred and the KMAC unit needs to be reset (1),
   * Examples for such faults include i) TL-UL bus integrity fault ii)
   * storage errors in the shadow registers iii) errors in the message,
   * round, or key counter iv) any internal FSM entering an invalid state v)
   * an error in the redundant lfsr.
   */
  kDifKmacAlertFatalFault = 1 << 0,
  /**
   * An update error has occurred in the shadowed Control Register. KMAC
   * operation needs to be restarted by re-writing the Control Register.
   */
  kDifKmacAlertRecovCtrlUpdate = 1 << 1,
} dif_kmac_alert_faults_t;

typedef struct dif_kmac_status {
  /**
   * Sha3 state.
   */
  dif_kmac_sha3_state_t sha3_state;

  /**
   * Message FIFO entry count.
   */
  uint32_t fifo_depth;

  /**
   * Kmac fifo state.
   */
  dif_kmac_fifo_state_t fifo_state;

  /**
   * Kmac faults and errors state.
   */
  dif_kmac_alert_faults_t faults;
} dif_kmac_status_t;

/**
 * Configures KMAC with runtime information.
 *
 * @param kmac A KMAC handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_configure(dif_kmac_t *kmac, dif_kmac_config_t config);

/**
 * Encode a customization string (S).
 *
 * The length of the string must not exceed `kDifKmacMaxCustomizationStringLen`.
 *
 * Note that this function will encode `len` bytes from `data` regardless of
 * whether `data` is null-terminated or not.
 *
 * See NIST Special Publication 800-185 [2] for more information about the
 * customization string (S) parameter.
 *
 * @param data String to encode.
 * @param len Length of string to encode.
 * @param[out] out Encoded customization string.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_customization_string_init(
    const char *data, size_t len, dif_kmac_customization_string_t *out);

/**
 * Encode a function name (N).
 *
 * The length of the string must not exceed `kDifKmacMaxFunctionNameLen`.
 *
 * Note that this function will encode `len` bytes from `data` regardless of
 * whether `data` is null-terminated or not.
 *
 * See NIST Special Publication 800-185 [2] for more information about the
 * function name (N) parameter.
 *
 * @param data String to encode.
 * @param len Length of string to encode.
 * @param[out] out Encoded function name.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_function_name_init(const char *data, size_t len,
                                         dif_kmac_function_name_t *out);

/**
 * Start a SHA-3 operation.
 *
 * SHA-3 operations have a fixed output length.
 *
 * See NIST FIPS 202 [1] for more information about SHA-3.
 *
 * @param kmac A KMAC handle.
 * @param operation_state A KMAC operation state context.
 * @param mode The SHA-3 mode of operation.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_mode_sha3_start(
    const dif_kmac_t *kmac, dif_kmac_operation_state_t *operation_state,
    dif_kmac_mode_sha3_t mode);

/**
 * Start a SHAKE operation.
 *
 * SHAKE operations have a variable (XOF) output length.
 *
 * See NIST FIPS 202 [1] for more information about SHAKE.
 *
 * @param kmac A KMAC handle.
 * @param operation_state A KMAC operation state context.
 * @param mode The mode of operation.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_mode_shake_start(
    const dif_kmac_t *kmac, dif_kmac_operation_state_t *operation_state,
    dif_kmac_mode_shake_t mode);

/**
 * Start a cSHAKE operation.
 *
 * cSHAKE operations have a variable (XOF) output length.
 *
 * See NIST Special Publication 800-185 [2] for more information about cSHAKE.
 *
 * @param kmac A KMAC handle.
 * @param operation_state A KMAC operation state context.
 * @param mode The mode of operation.
 * @param n Function name (optional).
 * @param s Customization string (optional).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_mode_cshake_start(
    const dif_kmac_t *kmac, dif_kmac_operation_state_t *operation_state,
    dif_kmac_mode_cshake_t mode, const dif_kmac_function_name_t *n,
    const dif_kmac_customization_string_t *s);

/**
 * Start a KMAC operation.
 *
 * To use KMAC in eXtendable-Output Function (XOF) mode set the output length
 * (`l`) to 0. The output length must not be greater than
 * `kDifKmacMaxOutputLenWords`.
 *
 * The key provided must have at least as many bits as the security strength
 * of the `mode`.
 *
 * See NIST Special Publication 800-185 [2] for more information about KMAC.
 *
 * @param kmac A KMAC handle.
 * @param operation_state A KMAC operation state context.
 * @param mode The mode of operation.
 * @param l Output length (number of 32-bit words that will be 'squeezed').
 * @param k Pointer to secret key.
 * @param s Customization string (optional).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_mode_kmac_start(
    const dif_kmac_t *kmac, dif_kmac_operation_state_t *operation_state,
    dif_kmac_mode_kmac_t mode, size_t l, const dif_kmac_key_t *k,
    const dif_kmac_customization_string_t *s);

/**
 * Absorb bytes from the message provided.
 *
 * If `processed` is non-NULL, then this function will write the remaining
 * space in the FIFO and update `processed` with the number of bytes written.
 * The caller should adjust the `msg` pointer and `len` parameters and call
 * again as needed until all input has been written.
 *
 * If `processed` is NULL, then this function will block until the entire
 * message has been processed or an error occurs.
 *
 * If big-endian mode is enabled for messages (`message_big_endian`) only the
 * part of the message aligned to 32-bit word boundaries will be byte swapped.
 * Unaligned leading and trailing bytes will be written into the message as-is.
 *
 * @param kmac A KMAC handle.
 * @param operation_state A KMAC operation state context.
 * @param msg Pointer to data to absorb.
 * @param len Number of bytes of data to absorb.
 * @param[out] processed Number of bytes processed (optional).
 * @preturn The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_absorb(const dif_kmac_t *kmac,
                             dif_kmac_operation_state_t *operation_state,
                             const void *msg, size_t len, size_t *processed);

/**
 * Squeeze bytes into the output buffer provided.
 *
 * Requesting a squeeze operation will prevent any further absorption operations
 * from taking place.
 *
 * If `kDifKmacIncomplete` is returned then the hardware is currently
 * recomputing the state and the output was only partially written. The output
 * pointer and length should be updated according to the number of bytes
 * processed and the squeeze operation continued at a later time.
 *
 * If `processed` is not provided then this function will block until `len`
 * bytes have been written to `out` or an error occurs.
 *
 * @param kmac A KMAC handle.
 * @param operation_state A KMAC operation state context.
 * @param[out] out Pointer to output buffer.
 * @param[out] len Number of 32-bit words to write to output buffer.
 * @param[out] processed Number of 32-bit words written to output buffer
 * (optional).
 * @preturn The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_squeeze(const dif_kmac_t *kmac,
                              dif_kmac_operation_state_t *operation_state,
                              uint32_t *out, size_t len, size_t *processed);

/**
 * Ends a squeeze operation and resets the hardware so it is ready for a new
 * operation.
 *
 * @param kmac A KMAC handle.
 * @param operation_state A KMAC operation state context.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_end(const dif_kmac_t *kmac,
                          dif_kmac_operation_state_t *operation_state);

/**
 * Read the kmac error register to get the error code indicated the interrupt
 * state.
 *
 * This function should be called in case of any of the `start` functions
 * returns `kDifError`.
 *
 * @param kmac A KMAC handle.
 * @param[out] error The current error code.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_get_error(const dif_kmac_t *kmac,
                                dif_kmac_error_t *error);

/**
 * Clear the current error code and reset the state machine to the idle state
 * ready to accept new operations.
 *
 * The state of any in-progress operation will be lost and the operation will
 * need to be restarted.
 *
 * @param kmac A KMAC handle.
 * @param operation_state A KMAC operation state context.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_reset(const dif_kmac_t *kmac,
                            dif_kmac_operation_state_t *operation_state);

/**
 * Fetch the current status of the message FIFO used to buffer absorbed data.
 *
 * @param kmac A KMAC handle.
 * @param[out] kmac_status The kmac status struct.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_get_status(const dif_kmac_t *kmac,
                                 dif_kmac_status_t *kmac_status);

/**
 * Returns the current value of the refresh hash counter.
 *
 * @param kmac A KMAC handle.
 * @param hash_ctr The hash counter value that is returned.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_get_hash_counter(const dif_kmac_t *kmac,
                                       uint32_t *hash_ctr);

/**
 * Reports whether or not the KMAC configuration register is locked.
 *
 * If writes to the KMAC configuration register are disabled (locked) then it is
 * not possible to change any configuration parameters or start a new operation.
 * The configuration register is locked when an operation has been started and
 * is unlocked again when it completes.
 *
 * @param kmac A KMAC handle.
 * @param[out] is_locked Out-param reporting the lock state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_config_is_locked(const dif_kmac_t *kmac, bool *is_locked);

/**
 * Poll until a given flag in the status register is set.
 *
 * @param kmac A KMAC handle.
 * @param flag the
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_poll_status(const dif_kmac_t *kmac, uint32_t flag);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_KMAC_H_
