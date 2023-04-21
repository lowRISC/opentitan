// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_OTP_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_OTP_CTRL_H_

/**
 * @file
 * @brief <a href="/hw/ip/otp_ctrl/doc/">OTP Controller</a> Device Interface
 * Functions
 */

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_otp_ctrl_autogen.h"

// Header Extern Guard (so header can be used from C and C++)
#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A partition within OTP memory.
 */
typedef enum dif_otp_ctrl_partition {
  /**
   * The vendor test area.
   *
   * This partition is reserved for macro-specific smoke tests.
   */
  kDifOtpCtrlPartitionVendorTest,
  /**
   * The creator software configuration area.
   *
   * This partition contains device-specific calibration data.
   */
  kDifOtpCtrlPartitionCreatorSwCfg,
  /**
   * The owner software configuration area.
   *
   * This partition contains data to e.g. enable ROM hardening features.
   */
  kDifOtpCtrlPartitionOwnerSwCfg,
  /**
   * The hardware configuration area.
   */
  kDifOtpCtrlPartitionHwCfg,
  /**
   * The device lifecycle area.
   */
  kDifOtpCtrlPartitionLifeCycle,
  /**
   * Scrambled partition 0.
   *
   * This partition contains TEST lifecycle state unlock tokens.
   */
  kDifOtpCtrlPartitionSecret0,
  /**
   * Scrambled partition 1.
   *
   * This partition contains SRAM and flash scrambling keys.
   */
  kDifOtpCtrlPartitionSecret1,
  /**
   * Scrambled partition 2.
   *
   * This partition contains the RMA unlock token and the CreatorRootKey.
   */
  kDifOtpCtrlPartitionSecret2,
} dif_otp_ctrl_partition_t;

/**
 * Runtime configuration for OTP.
 *
 * This struct describes runtime information for one-time configuration of the
 * hardware.
 */
typedef struct dif_otp_ctrl_config {
  /**
   * The timeout for an integrity or consistency check to succeed, in cycles.
   *
   * 100'000 is recommended as a minimum safe value.
   */
  uint32_t check_timeout;
  /**
   * A mask for the pseudo-random integrity check period.
   *
   * The value of this mask limits the period of the integrity check; when the
   * pseudo-random period is computed, this mask is applied to limit it. For
   * example, a value of 0x3'ffff would correspond to a maximum period of about
   * 2.8s at 24MHz.
   *
   * A value of zero disables the check.
   */
  uint32_t integrity_period_mask;
  /**
   * A mask for the pseudo-random consistency check period.
   *
   * The value of this mask limits the period of the consistency check; when the
   * pseudo-random period is computed, this mask is applied to limit it. For
   * example, a value of 0x3ff'ffff would correspond to a maximum period of
   * about 716s at 24MHz.
   *
   * A value of zero disables the check.
   */
  uint32_t consistency_period_mask;
} dif_otp_ctrl_config_t;

/**
 * A hardware-level status code.
 */
typedef enum dif_otp_ctrl_status_code {
  // NOTE: This enum's API *requires* that all "error"-like codes (that is,
  // those which have associated cause registers) be a prefix of the enum
  // values.
  //
  // Note furthermore that these enum variants are intended as bit indices, so
  // their values should not be randomized.
  /**
   * Indicates an error occurred in the `VendorTest` partition.
   */
  kDifOtpCtrlStatusCodeVendorTestError = 0,
  /**
   * Indicates an error occurred in the `CreatorSwCfg` partition.
   */
  kDifOtpCtrlStatusCodeCreatorSwCfgError,
  /**
   * Indicates an error occurred in the `OwnerSwCfg` partition.
   */
  kDifOtpCtrlStatusCodeOwnerSwCfgError,
  /**
   * Indicates an error occurred in the `HwCfg` partition.
   */
  kDifOtpCtrlStatusCodeHwCfgError,
  /**
   * Indicates an error occurred in the `LifeCycle` partition.
   */
  kDifOtpCtrlStatusCodeLifeCycleError,
  /**
   * Indicates an error occurred in the `Secret0` partition.
   */
  kDifOtpCtrlStatusCodeSecret0Error,
  /**
   * Indicates an error occurred in the `Secret1` partition.
   */
  kDifOtpCtrlStatusCodeSecret1Error,
  /**
   * Indicates an error occurred in the `Secret2` partition.
   */
  kDifOtpCtrlStatusCodeSecret2Error,
  /**
   * Indicates an error occurred in the direct access interface.
   */
  kDifOtpCtrlStatusCodeDaiError,
  /**
   * Indicates an error occurred in the lifecycle interface.
   */
  kDifOtpCtrlStatusCodeLciError,
  /**
   * This is not a status code; rather, it represents the last error code which
   * has a corresponding "cause" register.
   *
   * See `dif_otp_ctrl_status_t` for information on how to use this.
   */
  kDifOtpCtrlStatusCodeHasCauseLast = kDifOtpCtrlStatusCodeLciError,
  /**
   * Indicates that an integrity or consistency check has timed out.
   *
   * This error is unrecoverable.
   */
  kDifOtpCtrlStatusCodeTimeoutError,
  /**
   * Indicates that the LFSR that generates pseudo-random integrity and
   * consistency checks is in a bad state.
   *
   * This error is unrecoverable.
   */
  kDifOtpCtrlStatusCodeLfsrError,
  /**
   * Indicates that the scrambling hardware is in a bad state.
   *
   * This error is unrecoverable.
   */
  kDifOtpCtrlStatusCodeScramblingError,
  /**
   * Indicates that the key derivation hardware is in a bad state.
   *
   * This error is unrecoverable.
   */
  kDifOtpCtrlStatusCodeKdfError,
  /**
   * Indicates a bus integrity error.
   *
   * This error will raise an alert.
   */
  kDifOtpCtrlStatusCodeBusIntegError,
  /**
   * Indicates that the direct access interface is idle.
   */
  kDifOtpCtrlStatusCodeDaiIdle,
  /**
   * Indicates that an integrity or consistency check is currently pending.
   */
  kDifOtpCtrlStatusCodeCheckPending,
} dif_otp_ctrl_status_code_t;

/**
 * A hardware-level error code, associated with a particular error defined in
 * `dif_otp_ctrl_status_t`.
 */
typedef enum dif_otp_ctrl_error {
  /**
   * Indicates no error.
   */
  kDifOtpCtrlErrorOk,
  /**
   * Indicates that an OTP macro command was invalid or did not
   * complete successfully.
   *
   * This error indicates non-recoverable hardware malfunction.
   */
  kDifOtpCtrlErrorMacroUnspecified,
  /**
   * Indicates a recoverable error during a read operation.
   *
   * A followup read should work as expected.
   */
  kDifOtpCtrlErrorMacroRecoverableRead,
  /**
   * Indicates an unrecoverable error during a read operation.
   *
   * This error indicates non-recoverable hardware malfunction.
   */
  kDifOtpCtrlErrorMacroUnrecoverableRead,
  /**
   * Indicates that the blank write check failed during a write operation.
   */
  kDifOtpCtrlErrorMacroBlankCheckFailed,
  /**
   * Indicates a locked memory region was accessed.
   */
  kDifOtpCtrlErrorLockedAccess,
  /**
   * Indicates a parity, integrity or consistency check failed in the buffer
   * registers.
   *
   * This error indicates non-recoverable hardware malfunction.
   */
  kDifOtpCtrlErrorBackgroundCheckFailed,
  /**
   * Indicates that the FSM of the controller is in a bad state or that the
   * controller's FSM has been moved into its terminal state due to escalation
   * via the alert subsystem.
   *
   * This error indicates that the device has been glitched by an attacker.
   */
  kDifOtpCtrlErrorFsmBadState,
} dif_otp_ctrl_error_t;

/**
 * The overall status of the OTP controller.
 *
 * See `dif_otp_ctrl_get_status()`.
 */
typedef struct dif_otp_ctrl_status {
  /**
   * Currently active statuses, given as a bit vector. To check whether a
   * particular status code was returned, write
   *
   *   bool has_code = (status.codes >> kMyStatusCode) & 1;
   *
   * Note that it is possible to quickly check that the controller is idle and
   * error-free by writing
   *
   *   bool is_ok = status.codes == (1 << kDifOtpStatusCodeDaiIdle);
   */
  uint32_t codes;
  /**
   * A list of root causes for each error status code.
   *
   * If the error status code `error` is present in `codes`, and
   * `error <= kDifOtpCtrlStatusCodeHasCauseLast`, then `causes[error]`
   * will contain its root cause.
   */
  dif_otp_ctrl_error_t causes[kDifOtpCtrlStatusCodeHasCauseLast + 1];
} dif_otp_ctrl_status_t;

/**
 * Configures OTP with runtime information.
 *
 * This function should need to be called at most once for the lifetime of
 * `otp`.
 *
 * @param otp An OTP handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_configure(const dif_otp_ctrl_t *otp,
                                    dif_otp_ctrl_config_t config);

/**
 * Runs an integrity check on the OTP hardware.
 *
 * This function can be used to trigger an integrity check independent of the
 * pseudo-random hardware-generated checks.
 *
 * @param otp An OTP handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_check_integrity(const dif_otp_ctrl_t *otp);

/**
 * Runs a consistency check on the OTP hardware.
 *
 * This function can be used to trigger a consistency check independent of the
 * pseudo-random hardware-generated checks.
 *
 * @param otp An OTP handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_check_consistency(const dif_otp_ctrl_t *otp);

/**
 * Locks out `dif_otp_ctrl_configure()` function.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDifOtpCtrlOk`.
 *
 * @param otp An OTP handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_lock_config(const dif_otp_ctrl_t *otp);

/**
 * Checks whether `dif_otp_ctrl_configure()` function is locked-out.
 *
 * @param otp An OTP handle.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_config_is_locked(const dif_otp_ctrl_t *otp,
                                           bool *is_locked);

/**
 * Locks out `dif_otp_ctrl_check_*()` functions.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDifOtpCtrlOk`.
 *
 * @param otp An OTP handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_lock_check_trigger(const dif_otp_ctrl_t *otp);

/**
 * Checks whether the `dif_otp_ctrl_check_*()` functions are locked-out.
 *
 * @param otp An OTP handle.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_check_trigger_is_locked(const dif_otp_ctrl_t *otp,
                                                  bool *is_locked);

/**
 * Locks out reads to a SW partition.
 *
 * This function should only be called on SW partitions; doing otherwise will
 * return an error.
 *
 * Note that this is distinct from the write-locking performed by calling
 * `dif_otp_ctrl_dai_digest()`. In particular, the effects of this function will
 * not persist past a system reset.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDifOtpCtrlOk`.
 *
 * @param otp An OTP handle.
 * @param partition The SW partition to lock.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_lock_reading(const dif_otp_ctrl_t *otp,
                                       dif_otp_ctrl_partition_t partition);

/**
 * Checks whether reads to a SW partition are locked out.
 *
 * This function should only be called on SW partitions; doing otherwise will
 * return an error.
 *
 * @param otp An OTP handle.
 * @param partition the SW partition to check for locking.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_reading_is_locked(const dif_otp_ctrl_t *otp,
                                            dif_otp_ctrl_partition_t partition,
                                            bool *is_locked);

/**
 * Gets the current status of the OTP controller.
 *
 * @param otp An OTP handle.
 * @param[out] status Out-param for the controller's status.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_get_status(const dif_otp_ctrl_t *otp,
                                     dif_otp_ctrl_status_t *status);

/**
 * Calculates a `relative_address` with respect to a `partition` start
 * address.
 *
 * @param partition The partition to use to calculate the reference start
 * address.
 * @param abs_address Input address relative to the OTP memory start address.
 * @param[out] relative_address The result relative address with respect to the
 * `partition` start address.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_relative_address(dif_otp_ctrl_partition_t partition,
                                           uint32_t abs_address,
                                           uint32_t *relative_address);

/**
 * Schedules a read on the Direct Access Interface.
 *
 * Reads are performed relative to a partition; `address` should be given
 * relative to the start of `partition`. An error is returned for out-of-bounds
 * access.
 *
 * Furthermore, `address` must be well-aligned: it must be four-byte aligned for
 * normal partitions and eight-byte-aligned for secret partitions. An error is
 * returned for unaligned access.
 *
 * @param otp An OTP handle.
 * @param partition The partition to read from.
 * @param address A partition-relative address to read from.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_dai_read_start(const dif_otp_ctrl_t *otp,
                                         dif_otp_ctrl_partition_t partition,
                                         uint32_t address);

/**
 * Gets the result of a completed 32-bit read operation on the Direct Access
 * Interface.
 *
 * Whether this function or its 64-bit variant should be called is dependent on
 * the most recent partition read from.
 *
 * @param otp An OTP handle.
 * @param[out] value Out-param for the read value.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_dai_read32_end(const dif_otp_ctrl_t *otp,
                                         uint32_t *value);

/**
 * Gets the result of a completed 64-bit read operation on the Direct Access
 * Interface.
 *
 * Whether this function or its 32-bit variant should be called is dependent on
 * the most recent partition read from.
 *
 * @param otp An OTP handle.
 * @param[out] value Out-param for the read value.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_dai_read64_end(const dif_otp_ctrl_t *otp,
                                         uint64_t *value);

/**
 * Schedules a 32-bit write on the Direct Access Interface.
 *
 * Writes are performed relative to a partition; `address` should be given
 * relative to the start of `partition`. An error is returned for out-of-bounds
 * access.
 *
 * Furthermore, `address` must be four-byte-aligned, and `partition` must not be
 * a secret partition. An error is returned if neither condition is met.
 *
 * Note that this function cannot be used to program the digest at the end of a
 * `SW` partition; `dif_otp_ctrl_dai_digest()` must be used instead.
 *
 * @param otp An OTP handle.
 * @param partition The partition to program.
 * @param address A partition-relative address to program.
 * @param value The value to program into the OTP.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_dai_program32(const dif_otp_ctrl_t *otp,
                                        dif_otp_ctrl_partition_t partition,
                                        uint32_t address, uint32_t value);

/**
 * Schedules a 64-bit write on the Direct Access Interface.
 *
 * Writes are performed relative to a partition; `address` should be given
 * relative to the start of `partition`. An error is returned for out-of-bounds
 * access.
 *
 * Furthermore, `address` must be eight-byte-aligned, and `partition` must be
 * a secret partition. An error is returned if neither condition is met.
 *
 * @param otp An OTP handle.
 * @param partition The partition to program.
 * @param address A partition-relative address to program.
 * @param value The value to program into the OTP.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_dai_program64(const dif_otp_ctrl_t *otp,
                                        dif_otp_ctrl_partition_t partition,
                                        uint32_t address, uint64_t value);

/**
 * Schedules a hardware digest operation on the Direct Access Interface.
 *
 * **This operation will also lock writes for the given partition.**
 *
 * If `partition` is a SW partition, `digest` must be non-zero; if it is a
 * partition with a hardware-managed digest, `digest` *must* be zero (since the
 * digest will be generated by the hardware). An error is returned if either
 * precondition is not met.
 *
 * This function does not work with the lifecycle state partition, and will
 * return an error in that case.
 *
 * @param otp An OTP handle.
 * @param partition The partition to digest and lock.
 * @param digest The digest to program (for SW partitions).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_dai_digest(const dif_otp_ctrl_t *otp,
                                     dif_otp_ctrl_partition_t partition,
                                     uint64_t digest);

/**
 * Checks if the digest value for the given partition has been computed. Once a
 * digest has been computed for a partition, the partition is write-locked
 * (additionally, read-locked if the partition is secret).
 *
 * The lifecycle partition does not have a digest, and checking if this region
 * has a computed digest will return an error.
 *
 * @param otp An OTP handle.
 * @param partition The partition to check the digest of.
 * @param[out] is_computed Indicates if the digest has been computed.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_is_digest_computed(const dif_otp_ctrl_t *otp,
                                             dif_otp_ctrl_partition_t partition,
                                             bool *is_computed);

/**
 * Gets the buffered digest value for the given partition.
 *
 * Note that this value is only updated when the device is reset; if the digest
 * has not been computed yet, or has been computed but not since device reset,
 * this function will return an error.
 *
 * The lifecycle partition does not have a digest and will result in an error
 * being returned.
 *
 * @param otp An OTP handle.
 * @param partition The partition to get a digest for.
 * @param[out] digest Out-param for the digest.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_get_digest(const dif_otp_ctrl_t *otp,
                                     dif_otp_ctrl_partition_t partition,
                                     uint64_t *digest);

/**
 * Performs a memory-mapped read of the given partition, if it supports them.
 *
 * In particular, this function will read `len` words, starting at `address`,
 * relative to the start of `partition`.
 *
 * The same caveats for `dif_otp_ctrl_dai_read_start()` apply to `address`; in
 * addition, `address + len` must also be in-range and must not overflow.
 *
 * This function will block until the read completes, unlike Direct Access
 * Interface functions.
 *
 * @param otp An OTP handle.
 * @param partition The partition to read from.
 * @param address A partition-relative address to read from.
 * @param[out] buf A buffer of words to write read values to.
 * @param len The number of words to read.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_otp_ctrl_read_blocking(const dif_otp_ctrl_t *otp,
                                        dif_otp_ctrl_partition_t partition,
                                        uint32_t address, uint32_t *buf,
                                        size_t len);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_OTP_CTRL_H_
