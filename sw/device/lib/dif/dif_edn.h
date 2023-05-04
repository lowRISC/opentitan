// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_EDN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_EDN_H_

/**
 * @file
 * @brief <a href="/hw/ip/edn/doc/">Entropy Distribution Network</a> Device
 * Interface Functions
 *
 * This API implements the interface for the Entropy Distribution Network (EDN)
 * hardware.
 *
 * There are two main modes of operation:
 *
 * - boot-time: EDN configures the associated CSRNG instance to fetch pre-FIPS
 *   entropy immediately at boot-time or after reset.
 * - auto refresh: EDN sends reseed and generate commands to the associated
 *   CSRNG instance. The API allows the user to set the CSRNG instantiate,
 *   reseed and generate para meters, as well as the reseed frequency.
 */

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_edn_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Maximum seed material number of uint32_t words supported in CSRNG
   * instantiate and seed commands.
   */
  kDifEntropySeedMaterialMaxWordLen = 12,
};

enum {
  /**
   * Csrng commands
   */
  kDifEdnCmdInstantiate = 1,
  kDifEdnCmdReseed = 2,
  kDifEdnCmdGenerate = 3
};

/**
 * CSRNG seed material for instantiate, reseed and generate commands.
 */
typedef struct dif_edn_seed_material {
  /**
   * Number of uint32_t words in `data`. Up to
   * `kDifEntropySeedMaterialMaxWordLen` words can be set to initialize or
   * reseed the CSRNG. CSRNG will extend the `data` to zeros if the provided
   * value is less than kDifEntropySeedMaterialMaxWordLen.
   */
  size_t len;
  /**
   * Seed material used in CSRNG instantiate, reseed or generate call.
   */
  uint32_t data[kDifEntropySeedMaterialMaxWordLen];
} dif_edn_seed_material_t;

/**
 * CSRNG command parameters for instantiate, reseed and generate commands.
 */
typedef struct dif_edn_cmd {
  /**
   * The CSRNG application interface command header. For details, refer to the
   * CSRNG documentation.
   */
  uint32_t cmd;
  /**
   * Optional seed material.
   */
  dif_edn_seed_material_t seed_material;
} dif_edn_cmd_t;

/**
 * Auto-generate EDN module configuration parameters.
 */
typedef struct dif_edn_auto_params {
  /**
   * CSRNG instantiate command material.
   */
  dif_edn_cmd_t instantiate_cmd;
  /**
   * CSRNG reseed command material.
   */
  dif_edn_cmd_t reseed_cmd;
  /**
   * CSRNG generate command material.
   */
  dif_edn_cmd_t generate_cmd;
  /**
   * Number of generate calls that can be made before a reseed request is made.
   */
  uint32_t reseed_interval;
} dif_edn_auto_params_t;

/**
 * EDN Status flags.
 */
typedef enum dif_edn_status {
  /**
   * Device is ready to receive a command.
   */
  kDifEdnStatusReady,
  /**
   * Device has recieved an ACK from the CSRNG block.
   */
  kDifEdnStatusCsrngAck,
} dif_edn_status_t;

/**
 * Enumeration of EDN FIFOs, which indicates which part of the hardware
 * produced an error.
 */
typedef enum dif_edn_fifo {
  kDifEdnFifoReseedCmd,
  kDifEdnFifoGenerateCmd,
} dif_edn_fifo_t;

/**
 * Enumeration of EDN FIFO errors.
 */
typedef enum dif_edn_error {
  /**
   * Indicates an error in the command ack state machine.
   */
  kDifEdnErrorAckSm,
  /**
   * Indicates an error in the main state machine.
   */
  kDifEdnErrorMainSm,
  /**
   * Indicates an error in a hardened counter.
   */
  kDifEdnErrorCounterFault,
  /**
   * Indicates a write to a full FIFO occured.
   */
  kDifEdnErrorFifoWrite,
  /**
   * Indicates a read from an empty FIFO occured.
   */
  kDifEdnErrorFifoRead,
  /**
   * Indicates a FIFO was somehow both full and empty.
   */
  kDifEdnErrorFifoFullAndEmpty,
} dif_edn_error_t;

/**
 * CSRNG consume seed from entropy source enable.
 */
typedef enum dif_edn_entropy_src_toggle {
  /**
   * Seed material used as the only seed material.
   *
   * This configuration option will toggle the hardware state of the
   * CSRNG to non-FIPS compliant until it is re-instantiated.
   *
   * Note: Software may opt to XOR the seed material with a seed to implement
   * a software assisted FIPS mode of operation.
   */
  kDifEdnEntropySrcToggleDisable = 1,
  /**
   * Entropy source XOR'ed with the provided seed material.
   */
  kDifEdnEntropySrcToggleEnable = 0,
} dif_edn_entropy_src_toggle_t;

/**
 * Recoverable alerts emitted by the EDN.
 */
typedef enum dif_edn_recoverable_alert {
  /**
   * Indicates a bad value was written to the EDN_ENABLE field of the control
   * register.
   */
  kDifEdnRecoverableAlertBadEnable,
  /**
   * Indicates a bad value was written to the BOOT_REQ_MODE field of the control
   * register.
   */
  kDifEdnRecoverableAlertBadBootReqMode,
  /**
   * Indicates a bad value was written to the AUTO_REQ_MODE field of the
   * control register.
   */
  kDifEdnRecoverableAlertBadAutoReqMode,
  /**
   * Indicates a bad value was written to the CMD_FIFO_RST field of the
   * control register.
   */
  kDifEdnRecoverableAlertBadFifoClear,
  /**
   * Indicates the genbits bus saw two identical values, indicating a possible
   * attack.
   */
  kDifEdnRecoverableAlertRepeatedGenBits,
} dif_edn_recoverable_alert_t;

/**
 * Configures EDN with runtime information.
 *
 * This function should need to be called once for the lifetime of `handle`.
 *
 * @param edn An EDN handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_configure(const dif_edn_t *edn);

/**
 * Locks out EDN functionality.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDifEdnOk`.
 *
 * @param edn An EDN handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_lock(const dif_edn_t *edn);

/**
 * Checks whether this EDN is locked.
 *
 * @param edn An EDN handle.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_is_locked(const dif_edn_t *edn, bool *is_locked);

/**
 * Enables the EDN in boot-time mode.
 *
 * Each call to this function should be sequenced with a call to
 * `dif_edn_stop()`.
 *
 * @param edn An EDN handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_set_boot_mode(const dif_edn_t *edn);

/**
 * Enables the EDN in auto refresh mode.
 *
 * Each call to this function should be sequenced with a call to
 * `dif_edn_stop()`.
 *
 * @param edn An EDN handle.
 * @param config Auto request configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_set_auto_mode(const dif_edn_t *edn,
                                   dif_edn_auto_params_t config);

/**
 * Queries the EDN status flags.
 *
 * @param edn An EDN handle.
 * @param flag Status flag to query.
 * @param set Flag state (set/unset).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_get_status(const dif_edn_t *edn, dif_edn_status_t flag,
                                bool *set);

/**
 * Queries the EDN error flags.
 *
 * @param edn An EDN handle.
 * @param[out] unhealthy_fifos Bitset of FIFOs in an unhealthy state; indices
 * are `dif_edn_fifo_t`.
 * @param[out] errors Bitset of errors relating to the above FIFOs; indices are
 * `dif_edn_error_t`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_get_errors(const dif_edn_t *edn, uint32_t *unhealthy_fifos,
                                uint32_t *errors);

/**
 * Forces the status registers to indicate `fifo` as being in an unhealthy
 * state.
 *
 * @param edn An EDN handle
 * @param fifo The FIFO to mark as unhealthy.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_get_cmd_unhealthy_fifo_force(const dif_edn_t *edn,
                                                  dif_edn_fifo_t fifo);

/**
 * Forces the status registers to indicate a particular error cause.
 *
 * @param edn An EDN handle
 * @param error The error to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_get_cmd_error_force(const dif_edn_t *edn,
                                         dif_edn_error_t error);

/**
 * Returns an opaque blob indicating the main state machine's current state.
 *
 * @param csrng An EDN handle
 * @param state[out] The state machine state as an opaque blob.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_get_main_state_machine(const dif_edn_t *edn,
                                            uint32_t *state);

/**
 * Initializes CSRNG instance with a new seed value.
 *
 * `seed_material` is used as specified in NIST SP 800-90Ar1 section
 * 10.2.1.3.1.
 *
 * `seed_material` can be NULL, in which case CSRNG will use a zero
 * vector instead.
 *
 * @param edn An EDN handle.
 * @param entropy_src_enable Entropy source input enable.
 * @param seed_material Seed initialization parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_instantiate(
    const dif_edn_t *edn, dif_edn_entropy_src_toggle_t entropy_src_enable,
    const dif_edn_seed_material_t *seed_material);

/**
 * Reseeds CSRNG instance.
 *
 * When `seed_material.seed_material_len` is set to 0, only the entropy source
 * seed is used to reseed the instance, otherwise it will be XOR'ed with the
 * entropy source.
 *
 * @param edn An EDN handle.
 * @param seed_material Reseed parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_reseed(const dif_edn_t *edn,
                            const dif_edn_seed_material_t *seed_material);

/**
 * Updates CSRNG state.
 *
 * This function is similar to `dif_edn_reseed()`, except:
 *
 * - Only `seed_material.seed_material` is used in the update operation.
 * - The update operation does not reset the internal CSRNG reseed
 *   counter.
 *
 * @param edn An EDN handle.
 * @param seed_material Update parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_update(const dif_edn_t *edn,
                            const dif_edn_seed_material_t *seed_material);

/**
 * Requests cryptographic entropy bits from the CSRNG.
 *
 * The prediction resistance flag as specified in SP 800-90Ar1 section
 * 10.2.1.1 is not directly supported by the hardware. It is the
 * responsibility of the caller to reseed as needed before calling
 * this function.
 *
 * The CSRNG accepts generation requests with 128-bit granularity, with
 * a minimum 128-bit request size. This function will increase the size
 * of the request to align it to the nearest 128-bit boundary.
 *
 * @param edn An EDN handle.
 * @param len Number of uint32_t words to generate.
 * @return The result of the operation. KDifOutOfRange if the `len` parameter
 * results in a 128bit block level size greater than 0x800.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_generate_start(const dif_edn_t *edn, size_t len);

/**
 * Uninstantiates CSRNG.
 *
 * Resets the CSRNG instance. Values in the CSRNG are zeroed out. This
 * command effectively resets the CSRNG, clearing any errors that it
 * may have encountered due to processing or entropy source errors.
 *
 * @param edn An EDN handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_uninstantiate(const dif_edn_t *edn);

/**
 * Stops the current mode of operation and disables the entropy module.
 *
 * @param edn An EDN handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_stop(const dif_edn_t *edn);

/**
 * Gets the recoverable alerts currently recorded in the EDN block.
 *
 * This function returns the alerts in a bitset whose indices are given by
 * `dif_edn_recoverable_alert_t`.
 *
 * @param edn An EDN handle.
 * @param[out] alerts Bitset of alerts currently recorded.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_get_recoverable_alerts(const dif_edn_t *edn,
                                            uint32_t *alerts);

/**
 * Clears all recoverable alerts currently recorded in the EDN block.
 *
 * @param edn An EDN handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_clear_recoverable_alerts(const dif_edn_t *edn);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_EDN_H_
