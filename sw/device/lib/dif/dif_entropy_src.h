// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_ENTROPY_SRC_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_ENTROPY_SRC_H_

/**
 * @file
 * @brief <a href="/hw/ip/entropy_src/doc/">Entropy Source</a> Device Interface
 * Functions
 */

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_entropy_src_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Maximum pre-conditioning FIFO capacity.
   */
  // TODO: Synchronize value with hardware.
  kDifEntropySrcFifoMaxCapacity = 64,

  /**
   * Default firmware observe FIFO threshold.
   *
   * Default value used to trigger the `kDifEntropySrcIrqEsObserveFifoReady`
   * interrupt when enabled.
   */
  kDifEntropyFifoIntDefaultThreshold = 32,
};

/**
 * A statistical test on the bits emitted by an entropy source.
 */
typedef enum dif_entropy_src_test {
  /**
   * An SP 800-90B repetition count test.
   *
   * This test screens for stuck bits, or a total failure of the noise source.
   * This test fails if any sequence of bits repeats too many times in a row
   * for too many samples.
   */
  kDifEntropySrcTestRepCount,

  /**
   * An SP 800-90B adaptive proportion test.
   *
   * This test screens for statistical bias in the number of ones or zeros
   * output by the noise source.
   */
  kDifEntropySrcTestAdaptiveProportion,

  /**
   * A bucket test.
   *
   * This test looks for correlations between individual noise channels.
   */
  kDifEntropySrcTestBucket,

  /**
   * A "Markov" test.
   *
   * This test looks for unexpected first-order temporal correlations
   * between individual noise channels.
   */
  kDifEntropySrcTestMarkov,

  /**
   * A firmware-driven "mailbox" test.
   *
   * This test allows firmware to inspect 2kbit blocks of entropy, and signal
   * potential concerns to the hardware.
   */
  kDifEntropySrcTestMailbox,

  /**
   * A vendor-specific test implemented externally to the IP.
   */
  kDifEntropySrcTestVendorSpecific,

  /** \internal */
  kDifEntropySrcTestNumVariants,
} dif_entropy_src_test_t;

/**
 * A mode of operation for the entropy source.
 */
typedef enum dif_entropy_src_mode {
  /**
   * Indicates that the source is disabled.
   */
  kDifEntropySrcModeDisabled = 0,

  /**
   * The physical true random number generator mode.
   *
   * This mode uses a physical random noise generator for operation, and is
   * truly random. This noise generator is compatible with SP 800-90B.
   */
  kDifEntropySrcModePtrng = 1,

} dif_entropy_src_mode_t;

/**
 * A single-bit RNG mode, where only one bit is sampled.
 */
typedef enum dif_entropy_src_single_bit_mode {
  /**
   * Single-bit-mode, sampling the zeroth bit.
   */
  kDifEntropySrcSingleBitMode0 = 0,
  /**
   * Single-bit-mode, sampling the first bit.
   */
  kDifEntropySrcSingleBitMode1 = 1,
  /**
   * Single-bit-mode, sampling the second bit.
   */
  kDifEntropySrcSingleBitMode2 = 2,
  /**
   * Single-bit-mode, sampling the third bit.
   */
  kDifEntropySrcSingleBitMode3 = 3,
  /**
   * Indicates that single-bit-mode is disabled.
   */
  kDifEntropySrcSingleBitModeDisabled = 4,
} dif_entropy_src_single_bit_mode_t;

/**
 * Criteria used by various entropy source health tests to decide whether the
 * test has failed.
 */
typedef struct dif_entropy_src_test_config {
  /**
   * The size of the window to use for health tests, in bits.
   */
  uint16_t health_test_window;

  /**
   * The threshold for the repetition count test.
   */
  uint16_t rep_count_threshold;

  /**
   * The value range for the adaptive proportion test.
   *
   * The first value is the lower threshold; the second is the higher
   * threshold.
   */
  uint16_t adaptive_range[2];

  /**
   * The threshold for the bucket test.
   */
  uint16_t bucket_threshold;

  /**
   * The range for the "Markov" test.
   *
   * The first value is the lower threshold; the second is the higher
   * threshold.
   */
  uint16_t markov_range[2];

  /**
   * The value range for the vendor-specific test.
   *
   * The first value is the lower threshold; the second is the higher
   * threshold. However, vendors may interpret these values however they wish.
   */
  uint16_t vendor_range[2];
} dif_entropy_src_test_config_t;

/**
 * Firmware override parameters for an entropy source.
 */
typedef struct dif_entropy_src_fw_override_config {
  /**
   * Enables firmware monitoring of the post-health test entropy via
   * `dif_entropy_fifo_read()` calls.
   */
  bool enable;

  /**
   * Enables fimrware to insert entropy bits back into the pre-coditioner block
   * via `dif_entropy_fifo_write()` calls. This feature is useful when the
   * firmware is required to implement additional health checks, and to perform
   * known answer tests of the preconditioner function.
   *
   * This field requires `fw_override_enable` to be set.
   */
  bool entropy_insert_enable;

  /**
   * This field sets the depth of the observe FIFO hardware buffer used when
   * `fw_override_enable` is set to true.
   */
  uint8_t buffer_threshold;
} dif_entropy_src_fw_override_config_t;

/**
 * Runtime configuration for an entropy source.
 *
 * This struct describes runtime information for one-time configuration of the
 * hardware.
 */
typedef struct dif_entropy_src_config {
  /**
   * The mode to configure the entropy source in.
   */
  dif_entropy_src_mode_t mode;

  /**
   * Which health tests to enable.
   *
   * The variants of `dif_entropy_src_test` are used to index fields in this
   * array.
   *
   * Note that the value at `kDifEntropySrcTestMailbox` is ignored, since this
   * test is driven by the firmware, not the hardware.
   */
  bool tests[kDifEntropySrcTestNumVariants];

  /**
   * If set, all health-test-related registers will be cleared.
   */
  // TODO: Consider adding a separate setter for this config bit depending on
  // hardware behavior.
  bool reset_health_test_registers;

  /**
   * Specifies which single-bit-mode to use, if any at all.
   */
  dif_entropy_src_single_bit_mode_t single_bit_mode;

  /**
   * If set, entropy will be routed to a firmware-visible register instead of
   * being distributed to other hardware IPs.
   */
  // Open Question: Make this its own function? Seems like something that would
  // be toggled a lot.
  bool route_to_firmware;

  /**
   * If set, FIPS compliant entropy will be generated by this module after being
   * processed by an SP 800-90B compliant conditioning function.
   *
   * Software may opt for implementing FIPS mode of operation without hardware
   * support by setting this field to false. In such case, software is
   * responsible for implementing the conditioning function.
   */
  bool fips_mode;

  /**
   * Configuration parameters for health tests.
   */
  dif_entropy_src_test_config_t test_config;

  /**
   * Configuration parameters for firmware override buffer.
   */
  dif_entropy_src_fw_override_config_t fw_override;
} dif_entropy_src_config_t;

/**
 * Revision information for an entropy source.
 *
 * The fields of this struct have an implementation-specific interpretation.
 */
typedef struct dif_entropy_src_revision {
  uint8_t abi_revision;
  uint8_t hw_revision;
  uint8_t chip_type;
} dif_entropy_src_revision_t;

/**
 * Statistics on entropy source health tests.
 */
typedef struct dif_entropy_src_test_stats {
  /**
   * Watermarks indicating where the value emitted by a particular test has
   * ranged through; the low watermark is the lowest observed value, while the
   * high watermark is the highest.
   *
   * Each pair of watermarks is presented as a range from lowest to highest.
   */
  // TODO: Document behavior for repcnt and bucket tests.
  uint16_t watermarks[2][kDifEntropySrcTestNumVariants];

  /**
   * The number of times a particular test has failed.
   *
   * For tests that ensure the value lies in a range (such as the "Markov"
   * test), the array will contain the number of underflows and overflows of
   * this range, respectively; for tests that only have an upper range, the
   * first array element will be zeroed, and the second will be the number
   * of fails.
   *
   * For `dif_entropy_src_test.kDifEntropySrcTestRepCount` and
   * `dif_entropy_src_test.kDifEntropySrcTestBucket` the first array element
   * will be the number of fails, and the second will be zeroed.
   */
  uint32_t fails[2][kDifEntropySrcTestNumVariants];

  /**
   * The number of alerts emitted by a particular test.
   *
   * This has the same layout as `fails`.
   */
  uint8_t alerts[2][kDifEntropySrcTestNumVariants];
} dif_entropy_src_test_stats_t;

/**
 * Configures entropy source with runtime information.
 *
 * This function should need to be called once for the lifetime of `handle`.
 *
 * @param entropy An entropy source handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_entropy_src_configure(const dif_entropy_src_t *entropy_src,
                                       dif_entropy_src_config_t config);

/**
 * Queries the entropy source IP for its revision information.
 *
 * @param entropy An entropy source handle.
 * @param[out] revision Out-param for revision data.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_entropy_src_get_revision(const dif_entropy_src_t *entropy_src,
                                          dif_entropy_src_revision_t *revision);

/**
 * Queries the entropy source for health statistics.
 *
 * Calling this function also clears the relevant status registers.
 *
 * @param entropy An entropy source handle.
 * @param fips_mode The test mode to query statistics for.
 * @param[out] stats Out-param for stats data.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_entropy_src_get_stats(const dif_entropy_src_t *entropy_src,
                                       bool fips_mode,
                                       dif_entropy_src_test_stats_t *stats);

/**
 * Locks out entropy source functionality.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDifEntropySrcOk`.
 *
 * @param entropy An entropy source handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_entropy_src_lock(const dif_entropy_src_t *entropy_src);

/**
 * Checks whether this entropy source is locked.
 *
 * @param entropy An entropy source handle.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_entropy_src_is_locked(const dif_entropy_src_t *entropy_src,
                                       bool *is_locked);

/**
 * Checks to see if entropy is available for software consumption
 *
 * @param entropy An entropy source handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_entropy_src_avail(const dif_entropy_src_t *entropy_src);

/**
 * Reads off a word of entropy from the entropy source.
 *
 * @param entropy An entropy source handle.
 * @param[out] word Out-param for the entropy.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_entropy_src_read(const dif_entropy_src_t *entropy_src,
                                  uint32_t *word);

/**
 * Performs an override read from the entropy pipeline.
 *
 * Entropy source must be configured with firmware override mode enabled, and
 * the `len` parameter must be strictly less than the FIFO threshold set in the
 * firware override parameters.
 *
 * `buf` may be `NULL`; in this case, reads will be discarded.
 *
 * @param entropy An entropy source handle.
 * @param[out] buf A buffer to fill with words from the pipeline.
 * @param len The number of words to read into `buf`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_entropy_src_fifo_read(const dif_entropy_src_t *entropy_src,
                                       uint32_t *buf, size_t len);

/**
 * Performs an override write to the entropy pipeline.
 *
 * Entropy source must be configured with firmware override and insert mode
 * enabled, otherwise the function will return
 * `kDifBadArg`.
 *
 * @param entropy An entropy source handle.
 * @param buf A buffer to push words from into the pipeline.
 * @param len The number of words to read from `buf`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_entropy_src_fifo_write(const dif_entropy_src_t *entropy_src,
                                        const uint32_t *buf, size_t len);

/**
 * Disables the entropy module
 *
 * @param entropy An entropy source handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_entropy_src_disable(const dif_entropy_src_t *entropy_src);

/**
 * Get main entropy fsm idle status
 *
 * @param entropy An entropy source handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_entropy_src_get_idle(const dif_entropy_src_t *entropy_src);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_ENTROPY_SRC_H_
