// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_SKUS_EARLGREY_A0_SIVAL_BRINGUP_UTIL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_SKUS_EARLGREY_A0_SIVAL_BRINGUP_UTIL_H_

#include <stdint.h>

/**
 * A helper function to round up the passed in value to get it aligned to the
 * requested number of bits.
 *
 * @param input The 32-bit value to be aligned.
 * @param align_bits The alignment offset in number of bits.
 * @return The rounded up 32-bit value.
 */
uint32_t round_up_to(uint32_t input, uint32_t align_bits);

/**
 * Calculate the number of 4 byte words necessary to fit the passed in number
 * of bytes.
 *
 * @param bytes A number of bytes to round up to 32-bit words.
 * @return The rounded up size in 32-bit words.
 */
uint32_t size_to_words(uint32_t bytes);

/**
 * Retrieve the certificate size from the passed in pointer to its ASN.1 header.
 *
 * @param bytes A buffer of ASN.1 encoded bytes.
 * @return The size of the ASN.1 encoded certificate in bytes.
 */
uint32_t get_cert_size(const uint8_t *header);

/**
 * Prints a hash of the currently running personalization binary to the console.
 */
void log_self_hash(void);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_SKUS_EARLGREY_A0_SIVAL_BRINGUP_UTIL_H_
