// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_OTBN_TESTUTILS_RSA_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_OTBN_TESTUTILS_RSA_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_otbn.h"

/**
 * @file Run RSA on OTBN as a testing tool.
 * @brief This library is based on the DIF instead of a full OTBN driver, and
 * should be used for testing only. The library does not include message
 * hashing or encoding.
 */

/**
 * Load the RSA application into OTBN.
 *
 * @param otbn The OTBN context object.
 */
status_t otbn_testutils_rsa_load(dif_otbn_t *otbn);

/**
 * Start running modular exponentiation with the exponent 65537.
 *
 * Computes (in^65537) mod n. This corresponds to the core step in encryption
 * or signature verification, and is much faster than a general modular
 * exponentiation. 65537 is also called "F4" because it is the 4th Fermat
 * number (2^16 + 1).
 *
 * The RSA app should be loaded into OTBN with `otbn_testutils_rsa_load` before
 * calling this function.
 *
 * @param otbn The OTBN context object.
 * @param modulus The modulus (n).
 * @param in The plaintext message.
 * @param size_bytes The size of all buffers in bytes, i.e. the key/modulus
 *                   length (i.e. 128 for RSA 1024). Valid range: 32..512 in
 *                   32 byte-steps (i.e. RSA 256 to RSA 4096).
 */
status_t otbn_testutils_rsa_modexp_f4_start(dif_otbn_t *otbn,
                                            const uint8_t *modulus,
                                            const uint8_t *in,
                                            size_t size_bytes);

/**
 * Finish modular exponentiation with the exponent 65537.
 *
 * Waits for OTBN to complete and reads back the result of modular
 * exponentiation. Call only after `otbn_testutils_rsa_modexp_f4_start`.
 *
 * @param otbn The OTBN context object.
 * @param out The encrypted message.
 * @param size_bytes The size of all buffers in bytes, i.e. the key/modulus
 *                   length (i.e. 128 for RSA 1024). Valid range: 32..512 in
 *                   32 byte-steps (i.e. RSA 256 to RSA 4096).
 */
status_t otbn_testutils_rsa_modexp_f4_finalize(dif_otbn_t *otbn, uint8_t *out,
                                               size_t size_bytes);

/**
 * Start a constant-time modular exponentiation.
 *
 * Computes (in^d) mod n. This corresponds to the core step in decryption or
 * signature generation and can be very slow.
 *
 * The RSA app should be loaded into OTBN with `otbn_testutils_rsa_load` before
 * calling this function.
 *
 * @param otbn The OTBN context object.
 * @param modulus The modulus (n).
 * @param private_exponent The private exponent (d).
 * @param in The encrypted message.
 * @param out The decrypted (plaintext) message.
 * @param size_bytes The size of all buffers in bytes, i.e. the key/modulus
 *                   length (i.e. 128 for RSA 1024). Valid range: 32..512 in
 *                   32 byte-steps (i.e. RSA 256 to RSA 4096).
 */
status_t otbn_testutils_rsa_modexp_consttime_start(
    dif_otbn_t *otbn, const uint8_t *modulus, const uint8_t *private_exponent,
    const uint8_t *in, size_t size_bytes);
/**
 * Finish modular exponentiation with the exponent 65537.
 *
 * Waits for OTBN to complete and reads back the result of modular
 * exponentiation. Call only after `otbn_testutils_rsa_modexp_consttime_start`.
 *
 * @param otbn The OTBN context object.
 * @param out The encrypted message.
 * @param size_bytes The size of all buffers in bytes, i.e. the key/modulus
 *                   length (i.e. 128 for RSA 1024). Valid range: 32..512 in
 *                   32 byte-steps (i.e. RSA 256 to RSA 4096).
 */
status_t otbn_testutils_rsa_modexp_consttime_finalize(dif_otbn_t *otbn,
                                                      uint8_t *out,
                                                      size_t size_bytes);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_OTBN_TESTUTILS_RSA_H_
