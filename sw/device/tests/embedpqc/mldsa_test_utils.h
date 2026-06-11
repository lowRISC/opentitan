// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_EMBEDPQC_MLDSA_TEST_UTILS_H_
#define OPENTITAN_SW_DEVICE_TESTS_EMBEDPQC_MLDSA_TEST_UTILS_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define MLDSA_STACK_SIZE (64 * 1024)
extern uint8_t mldsa_stack[MLDSA_STACK_SIZE];

/**
 * Fills the custom stack buffer with a predefined pattern (0xA5) to allow
 * stack high-watermark usage measurement.
 */
void paint_stack(void);

/**
 * Analyzes the custom stack buffer to find the deepest modified address
 * (non-0xA5) and returns the maximum stack usage in bytes.
 *
 * @return Deepest stack usage in bytes.
 */
size_t get_max_stack_usage(void);

/**
 * Verbose array comparison helper that compares two byte buffers and logs
 * the index, got value, and expected value of the first mismatch encountered.
 *
 * @param got The byte buffer obtained.
 * @param expected The expected byte buffer.
 * @param len Length of the buffers to compare in bytes.
 * @return True if the buffers match exactly, False otherwise.
 */
bool check_arrays_eq_verbose(const uint8_t *got, const uint8_t *expected,
                             size_t len);

#endif  // OPENTITAN_SW_DEVICE_TESTS_EMBEDPQC_MLDSA_TEST_UTILS_H_
