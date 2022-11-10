// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_ENTROPY_SRC_KAT_IMPL_H_
#define OPENTITAN_SW_DEVICE_TESTS_ENTROPY_SRC_KAT_IMPL_H_

#include <stdbool.h>

#include "sw/device/lib/dif/dif_entropy_src.h"

/**
 * Runs known answer test for the entropy_src SHA-3 conditioner.
 *
 * This test uses the following SHA3 CAVP test vector:
 *
 * Msg=a90d2aa5b241e1ca9dab5b6dc05c3e2c93fc5a2210a6315d60f9b791b36b560d70e135ef8e7dba9441b74e53dab0606b
 * MD=4a16881ce156f45fdfdb45088e3f23be1b4c5a7a6a35315d36c51c75f275733319aca185d4ab33130ffe45f751f1bbc5
 *
 * See:
 * https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing
 *
 * This test stops all the entropy blocks (entropy_src, csrng, edn0, edn1), and
 * configures the entropy_src in firmware override mode to inject data into the
 * conditioner and inspect its output. The test throws a test assertion on any
 * failures.
 *
 * The caller should use one of the functions from the entropy_testutils module
 * to configure the entropy blocks after running this test.
 *
 * @param entropy_src Entropy source handle.
 */
void entropy_src_kat_test(dif_entropy_src_t *entropy_src);

#endif  // OPENTITAN_SW_DEVICE_TESTS_ENTROPY_SRC_KAT_IMPL_H_
