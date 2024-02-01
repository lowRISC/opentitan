// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/* These assembly functions are used in the rv_core_ibex_rnd_test chip-level
 * test. Writing these functions in assembly guarantees that the memory reads
 * are a fixed number of instructions apart, independent of how the compiler
 * optimizes code. This is important because the RND status is low for only a
 * small number of cycles (10 cycles in the Verilator simulator). If we do not
 * write these in assembly, changes to the test, implementation or compiler
 * could affect whether the tests pass or not, which is de-risked to a certain
 * extent by using the assembly versions.
 */

#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"
#include "rv_core_ibex_regs.h"

/**
 * Read RND Data and immediately read RND status afterwards.
 *
 * @return the value of the RND status.
 */
  .globl rv_core_ibex_rnd_read_and_immediately_check_status
  .type rv_core_ibex_rnd_read_and_immediately_check_status, @function
rv_core_ibex_rnd_read_and_immediately_check_status:
  li t0, TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR // Load ibex base address
  lw t1, RV_CORE_IBEX_RND_DATA_REG_OFFSET(t0) // Read RND data
  lw a0, RV_CORE_IBEX_RND_STATUS_REG_OFFSET(t0) // Get RND status
  ret // Return status

/**
 * Read RND data to invalidate status, read status then read RND again,
 * followed by read status. If both status reads are low and you read the same
 * data then it means read data does not block when status is invalid. Check
 * that the RND status reads are equal and the invalid RND data read is zero.
 *
 * @return -1 if the second load does not equal the fourth or if the
 * intermediate RND read is not zero. Otherwise return the value of the RND
 * status.
 */
  .globl rv_core_ibex_check_rnd_read_possible_while_status_invalid
  .type rv_core_ibex_check_rnd_read_possible_while_status_invalid, @function
rv_core_ibex_check_rnd_read_possible_while_status_invalid:
  li t0, TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR // Load ibex base address
  lw t1, RV_CORE_IBEX_RND_DATA_REG_OFFSET(t0) // Read RND to invalidate status
  lw t2, RV_CORE_IBEX_RND_STATUS_REG_OFFSET(t0) // Get RND status
  lw t3, RV_CORE_IBEX_RND_DATA_REG_OFFSET(t0) // Read RND data
  lw a0, RV_CORE_IBEX_RND_STATUS_REG_OFFSET(t0) // Get RND status
  sub t2, t2, a0 // Calculate difference between first and last status
  or t2, t2, t3 // Check whether intermediate RND data is 0
  bnez t2, error_return // Check whether to return -1
  ret // Return status value
error_return:
  addi a0, x0, -1 // Put -1 in a0
  ret // Return -1
