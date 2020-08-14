// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Sends the LLVM profile buffer along with its length and CRC32.
 *
 * This function must be called at the end of a test. Note that this profile
 * data is raw and must be indexed before it can be used to generate coverage
 * reports.
 */
void test_coverage_send_buffer(void);
