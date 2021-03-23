// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_ENTROPY_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_ENTROPY_H_

/**
 * @file
 * @brief <a href="/hw/ip/entropy_src/doc/">Entropy Source</a> Device Interface
 * Functions
 */

#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_warn_unused_result.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Maximum pre-conditioning FIFO capacity.
   */
  // TODO: Synchronize value with hardware.
  kDifEntropyFifoMaxCapacity = 64,
};

/**
 * A toggle state: enabled, or disabled.
 *
 * This enum may be used instead of a `bool` when describing an enabled/disabled
 * state.
 */
typedef enum dif_entropy_toggle {
  /*
   * The "enabled" state.
   */
  kDifEntropyToggleEnabled,
  /**
   * The "disabled" state.
   */
  kDifEntropyToggleDisabled,
} dif_entropy_toggle_t;

/**
 * A statistical test on the bits emitted by an entropy source.
 */
typedef enum dif_entropy_test {
  /**
   * An SP 800-90B repetition count test.
   *
   * This test screens for stuck bits, or a total failure of the noise source.
   * This test fails if any sequence of bits repeats too many times in a row
   * for too many samples.
   */
  kDifEntropyTestRepCount,

  /**
   * An SP 800-90B adaptive proportion test.
   *
   * This test screens for statistical bias in the number of ones or zeros
   * output by the noise source.
   */
  kDifEntropyTestAdaptiveProportion,

  /**
   * A bucket test.
   *
   * This test looks for correlations between individual noise channels.
   */
  kDifEntropyTestBucket,

  /**
   * A "Markov" test.
   *
   * This test looks for unexpected first-order temporal correlations
   * between individual noise channels.
   */
  kDifEntropyTestMarkov,

  /**
   * A firmware-driven "mailbox" test.
   *
   * This test allows firmware to inspect 2kbit blocks of entropy, and signal
   * potential concerns to the hardware.
   */
  kDifEntropyTestMailbox,

  /**
   * A vendor-specific test implemented externally to the IP.
   */
  kDifEntropyTestVendorSpecific,

  /** \internal */
  kDifEntropyTestNumVariants,
} dif_entropy_test_t;

/**
 * A mode of operation for the entropy source.
 */
typedef enum dif_entropy_mode {
  /**
   * Indicates that the source is disabled.
   */
  kDifEntropyModeDisabled,

  /**
   * The physical true random number generator mode.
   *
   * This mode uses a physical random noise generator for operation, and is
   * truly random. This noise generator is compatible with SP 800-90B.
   */
  kDifEntropyModePtrng,

  /**
   * The Linear Feedback Shift Register (LFSR) mode.
   *
   * This mode is digital, and as such is only pseudo-random and intended
   * for test purposes only.
   *
   * In this mode, the `dif_entropy_config.lfsr_seed` value is used to
   * initialize the internal state of the LFSR.
   */
  kDifEntropyModeLfsr,
} dif_entropy_mode_t;

/**
 * A single-bit RNG mode, where only one bit is sampled.
 */
typedef enum dif_entropy_single_bit_mode {
  /**
   * Indicates that single-bit-mode is disabled.
   */
  kDifEntropySingleBitModeDisabled,

  /**
   * Single-bit-mode, sampling the zeroth bit.
   */
  kDifEntropySingleBitMode0,

  /**
   * Single-bit-mode, sampling the first bit.
   */
  kDifEntropySingleBitMode1,

  /**
   * Single-bit-mode, sampling the second bit.
   */
  kDifEntropySingleBitMode2,

  /**
   * Single-bit-mode, sampling the third bit.
   */
  kDifEntropySingleBitMode3,
} dif_entropy_single_bit_mode_t;

/**
 * Criteria used by various entropy source health tests to decide whether the
 * test has failed.
 */
typedef struct dif_entropy_test_config {
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
} dif_entropy_test_config_t;

/**
 * Hardware instantiation parameters for an entropy source.
 *
 * This struct describes information about the underlying hardware that is
 * not determined until the hardware design is used as part of a top-level
 * design.
 */
typedef struct dif_entropy_params {
  /**
   * The base address for the entropy source hardware registers.
   */
  mmio_region_t base_addr;
} dif_entropy_params_t;

/**
 * Runtime configuration for an entropy source.
 *
 * This struct describes runtime information for one-time configuration of the
 * hardware.
 */
typedef struct dif_entropy_config {
  /**
   * The mode to configure the entropy source in.
   */
  dif_entropy_mode_t mode;

  /**
   * Which health tests to enable.
   *
   * The variants of `dif_entropy_test` are used to index fields in this
   * array.
   *
   * Note that the value at `kDifEntropyTestMailbox` is ignored, since this test
   * is driven by the firmware, not the hardware.
   */
  bool tests[kDifEntropyTestNumVariants];

  /**
   * If set, all health-test-related registers will be cleared.
   */
  // TODO: Consider adding a separate setter for this config bit depending on
  // hardware behavior.
  bool reset_health_test_registers;

  /**
   * Specifies which single-bit-mode to use, if any at all.
   */
  dif_entropy_single_bit_mode_t single_bit_mode;

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
  dif_entropy_test_config_t test_config;

  /**
   * The rate at which the entropy bits are generated, in clock cycles.
   */
  uint16_t sample_rate;

  /**
   * Seed used to load into the LFSR initial state. The maximum allowable value
   * is 15. See `dif_entropy_mode.kDifEntropyModeLfsr` for more details.
   */
  uint16_t lfsr_seed;
} dif_entropy_config_t;

/**
 * A handle to an entropy source.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_entropy {
  dif_entropy_params_t params;
} dif_entropy_t;

/**
 * Revision information for an entropy source.
 *
 * The fields of this struct have an implementation-specific interpretation.
 */
typedef struct dif_entropy_revision {
  uint8_t abi_revision;
  uint8_t hw_revision;
  uint8_t chip_type;
} dif_entropy_revision_t;

/**
 * Statistics on entropy source health tests.
 */
typedef struct dif_entropy_test_stats {
  /**
   * Watermarks indicating where the value emitted by a particular test has
   * ranged through; the low watermark is the lowest observed value, while the
   * high watermark is the highest.
   *
   * Each pair of watermarks is presented as a range from lowest to highest.
   */
  // TODO: Document behavior for repcnt and bucket tests.
  uint16_t watermarks[2][kDifEntropyTestNumVariants];

  /**
   * The number of times a particular test has failed.
   *
   * For tests that ensure the value lies in a range (such as the "Markov"
   * test), the array will contain the number of underflows and overflows of
   * this range, respectively; for tests that only have an upper range, the
   * first array element will be zeroed, and the second will be the number
   * of fails.
   *
   * For `dif_entropy_test.kDifEntropyTestRepCount` and
   * `dif_entropy_test.kDifEntropyTestBucket` the first array element will
   * be the number of fails, and the second will be zeroed.
   */
  uint32_t fails[2][kDifEntropyTestNumVariants];

  /**
   * The number of alerts emitted by a particular test.
   *
   * This has the same layout as `fails`.
   */
  uint8_t alerts[2][kDifEntropyTestNumVariants];
} dif_entropy_test_stats_t;

/**
 * The result of an entropy source operation.
 */
typedef enum dif_entropy_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifEntropyOk = 0,
  /**
   * Indicates some unspecified failure.
   */
  kDifEntropyError = 1,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occured.
   */
  kDifEntropyBadArg = 2,
  /**
   * Indicates that this operation has been locked out, and can never
   * succeed until hardware reset.
   */
  kDifEntropyLocked = 3,
} dif_entropy_result_t;

/**
 * An entropy source interrupt request type.
 */
typedef enum dif_entropy_irq {
  /**
   * Indicates that bits of entropy are available to consume.
   */
  kDifEntropyIrqAvailable,

  /**
   * Indicates that the health test has failed and the alert count has been
   * met.
   */
  kDifEntropyIrqUnhealthy,

  /**
   * Indicates that an internal error occured in the FIFO, or if an illegal
   * state machine state is reached.
   */
  kDifEntropyIrqFatalError,
} dif_entropy_irq_t;

/**
 * A snapshot of the enablement state of the interrupts for an entropy source.
 *
 * This is an opaque type, to be used with the `dif_entropy_irq_disable_all()`
 * and `dif_entropy_irq_restore_all()` functions.
 */
typedef uint32_t dif_entropy_irq_snapshot_t;

/**
 * An entropy source alert type.
 */
typedef enum dif_entropy_alert {
  /**
   * Indicates that the health test criteria were not met.
   */
  kDifEntropyAlert,

  /**
   * Indicates that an internal error occurred.
   */
  kDifEntropyFatal,
} dif_entropy_alert_t;

/**
 * Creates a new handle for entropy source.
 *
 * This function does not actuate the hardware.
 *
 * @param params Hardware instantiation parameters.
 * @param[out] entropy Out param for the initialized handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_init(dif_entropy_params_t params,
                                      dif_entropy_t *entropy);

/**
 * Configures entropy source with runtime information.
 *
 * This function should need to be called once for the lifetime of `handle`.
 *
 * @param entropy An entropy source handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
// TODO: Should we have a separate function to clear the stats, or should
// that be handled by this function.
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_configure(const dif_entropy_t *entropy,
                                           dif_entropy_config_t config);

/**
 * Queries the entropy source IP for its revision information.
 *
 * @param entropy An entropy source handle.
 * @param[out] revision Out-param for revision data.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_get_revision(const dif_entropy_t *entropy,
                                              dif_entropy_revision_t *revision);

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
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_get_stats(const dif_entropy_t *entropy,
                                           bool fips_mode,
                                           dif_entropy_test_stats_t *stats);

/**
 * Locks out entropy source functionality.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDifEntropyOk`.
 *
 * @param entropy An entropy source handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_lock(const dif_entropy_t *entropy);

/**
 * Checks whether this entropy source is locked.
 *
 * @param entropy An entropy source handle.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_is_locked(const dif_entropy_t *entropy,
                                           bool *is_locked);

/**
 * Reads off a word of entropy from the entropy source.
 *
 * @param entropy An entropy source handle.
 * @param[out] word Out-param for the entropy.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_read(const dif_entropy_t *entropy,
                                      uint32_t *word);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param entropy An entropy source handle.
 * @param irq An interrupt type.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_irq_is_pending(const dif_entropy_t *entropy,
                                                dif_entropy_irq_t irq,
                                                bool *is_pending);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param entropy An entropy source handle.
 * @param irq An interrupt type.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_irq_acknowledge(const dif_entropy_t *entropy,
                                                 dif_entropy_irq_t irq);

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param entropy An entropy source handle.
 * @param irq An interrupt type.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_irq_get_enabled(const dif_entropy_t *entropy,
                                                 dif_entropy_irq_t irq,
                                                 dif_entropy_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param entropy An entropy source handle.
 * @param irq An interrupt type.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_irq_set_enabled(const dif_entropy_t *entropy,
                                                 dif_entropy_irq_t irq,
                                                 dif_entropy_toggle_t state);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param entropy An entropy source handle.
 * @param irq An interrupt type.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_irq_force(const dif_entropy_t *entropy,
                                           dif_entropy_irq_t irq);

/**
 * Disables all interrupts, optionally snapshotting all toggle state for later
 * restoration.
 *
 * @param entropy An entropy source handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_irq_disable_all(
    const dif_entropy_t *entropy, dif_entropy_irq_snapshot_t *snapshot);

/**
 * Restores interrupts from the given snapshot.
 *
 * This function can be used with `dif_entropy_irq_disable_all()` to temporary
 * interrupt save-and-restore.
 *
 * @param entropy An entropy source handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_irq_restore_all(
    const dif_entropy_t *entropy, const dif_entropy_irq_snapshot_t *snapshot);

/**
 * Forces a particular alert, causing it to be emitted as if the hardware had
 * done so.
 *
 * @param entropy An entropy source handle.
 * @param alert An alert type.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_alert_force(const dif_entropy_t *entropy,
                                             dif_entropy_alert_t alert);

/**
 * Performs an override read from the entropy pipeline.
 *
 * This function pauses entropy flow out of the pre-conditioner FIFO and
 * instead flows words into `buf`. Normal operation of the entropy pipeline
 * will not resume until `dif_entropy_fifo_reconnect()` is called.
 *
 * `buf` may be `NULL`; in this case, reads will be discarded.
 *
 * @param entropy An entropy source handle.
 * @param[out] buf A buffer to fill with words from the pipeline.
 * @param len The number of words to read into `buf`.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_fifo_read(const dif_entropy_t *entropy,
                                           uint32_t *buf, size_t len);

/**
 * Performs an override write to the entropy pipeline.
 *
 * This function pauses entropy flow into the pre-conditioner FIFO and
 * instead flows words out of `buf`. Normal operation of the entropy pipeline
 * will not resume until `dif_entropy_fifo_reconnect()` is called.
 *
 * @param entropy An entropy source handle.
 * @param buf A buffer to push words from into the pipeline.
 * @param len The number of words to read from `buf`.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_fifo_write(const dif_entropy_t *entropy,
                                            const uint32_t *buf, size_t len);

/**
 * Gets the current number of entries in the pre-conditioner FIFO.
 *
 * This function pauses the flow through the FIFO.
 *
 * @param entropy An entropy source handle.
 * @param[out] len The number of words in the FIFO.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_fifo_get_len(const dif_entropy_t *entropy,
                                              uint8_t *len);

/**
 * Gets the current capacity of the pre-conditioner FIFO.
 *
 * @param entropy An entropy source handle.
 * @param[out] capacity The number of words of capacity in the FIFO.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_fifo_get_capacity(const dif_entropy_t *entropy,
                                                   uint8_t *capacity);

/**
 * Sets the current capacity of the pre-conditioner FIFO.
 *
 * The `capacity` value must be less or equal to the physical capacity
 * of the fifo, defined as `kDifEntropyFifoMaxCapacity`.
 *
 * @param entropy An entropy source handle.
 * @param capacity The new capacity for the FIFO.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_fifo_set_capacity(const dif_entropy_t *entropy,
                                                   uint8_t capacity);

/**
 * Reconnects the entropy pipeline after an operation that pauses it.
 *
 * This is a separate function call to avoid races between software and hardware
 * when performing multiple such operations, such as getting the length followed
 * by a read.
 *
 * @param entropy An entropy source handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_entropy_result_t dif_entropy_fifo_reconnect(const dif_entropy_t *entropy);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_ENTROPY_H_
