// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_HMAC_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_HMAC_TESTUTILS_H_

#include <assert.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_hmac.h"

/**
 * Timeouts to be used for different HMAC operations.
 *
 * All timeouts are calculated against the `kClockFreqCpuHz`, in order
 * to cover a range of targets. Please see:
 * https://docs.opentitan.org/hw/ip/hmac/doc/
 *
 * 10 cycles are added to the length of the corresponding operation as
 * described in the documentation. This is to cover any potential
 * inconsistencies or minor IP changes.
 *
 * To avoid cases with sub uS timeout due to very high clock frequency, we
 * guarantee 1uS minimal timeout by adding it in the end.
 */

/**
 * FIFO empty timeout.
 *
 * single HMAC block compression takes 80 cycles.
 */
#define HMAC_TESTUTILS_FIFO_EMPTY_USEC \
  (udiv64_slow((80 + 10) * 1000000, kClockFreqCpuHz, NULL) + 1)

/**
 * HMAC done timeout.
 *
 * Final hash calculation takes 360 cycles, which consists of one block
 * compression and extra HMAC computation.
 */
#define HMAC_TESTUTILS_FINISH_TIMEOUT_USEC \
  (udiv64_slow((360 + 10) * 1000000, kClockFreqCpuHz, NULL) + 1)

/**
 * Reference key and tag for testing from NIST.
 *
 * https://csrc.nist.gov/CSRC/media/Projects/
 * Cryptographic-Standards-and-Guidelines/documents/examples/HMAC_SHA256.pdf
 *
 * Key Length: 100
 * Tag length: 32
 *
 * When key is > than the block size, it should be hashed to obtain the block
 * sized key. Please refer to:
 * https://csrc.nist.gov/csrc/media/publications/fips/198/archive/
 * 2002-03-06/documents/fips-198a.pdf
 *
 * Specifically chapter 3 and 5 (Table 1).
 */

/**
 * This should be hashed with SHA-256 to generate the key.
 */
extern const uint8_t kRefHmacLongKey[100];

/**
 * Expected SHA digest for kRefHmacLongKey data above.
 */
extern const dif_hmac_digest_t kRefExpectedShaDigest;

/**
 * This is used as data for the MAC computation, using kRefExpectedShaDigest
 * as the key.
 */
extern const char kRefData[34];

/**
 * Expected MAC digest for kRefData data above.
 */
extern const dif_hmac_digest_t kRefExpectedHmacDigest;

/**
 * Reads and compares the actual sent message length against expected.
 *
 * The message length is provided in bits.
 *
 * @param hmac An HMAC handle.
 * @param expected_sent_bits Expected size of hashed data in bits.
 */
void hmac_testutils_check_message_length(const dif_hmac_t *hmac,
                                         uint64_t expected_sent_bits);

/**
 * Spins until the HMAC FIFO is empty, or has timed out.
 *
 * Internally uses `kHmacTestutilsFifoEmptyTimeoutUsec`.
 *
 * @param hmac An HMAC handle.
 */
void hmac_testutils_fifo_empty_polled(const dif_hmac_t *hmac);

/**
 * Spins until the HMAC has finished processing final hash, or timed out.
 *
 * Internally uses `kHmacTestutilsFinishTimeoutUsec`.
 *
 * @param hmac An HMAC handle.
 * @param digest_out HMAC final digest.
 */
void hmac_testutils_finish_polled(const dif_hmac_t *hmac,
                                  dif_hmac_digest_t *digest_out);

/**
 * Spins until HMAC has processed the final hash, and compares the digests.
 *
 * Convenience function that combines `hmac_testutils_finish_polled` and
 * and `CHECK_ARRAYS_EQ`.
 *
 * @param hmac An HMAC handle.
 * @param expected Expected HMAC final digest.
 */
void hmac_testutils_finish_and_check_polled(const dif_hmac_t *hmac,
                                            const dif_hmac_digest_t *expected);

/**
 * Loads entire message into the HMAC engine.
 *
 * Internally uses `hmac_testutils_fifo_empty_polled` after every push to
 * avoid the back pressure.
 *
 * @param hmac An HMAC handle.
 * @param data Data to be hashed.
 * @param len Size of the data to be hashed.
 */
void hmac_testutils_push_message(const dif_hmac_t *hmac, const char *data,
                                 size_t len);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_HMAC_TESTUTILS_H_
