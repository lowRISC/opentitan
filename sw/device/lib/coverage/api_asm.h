// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_COVERAGE_API_ASM_H_
#define OPENTITAN_SW_DEVICE_LIB_COVERAGE_API_ASM_H_

#ifdef OT_COVERAGE_INSTRUMENTED

/**
 * Initializes the coverage counter region in RAM to an "uncovered" state.
 *
 * The validity flag is set after initialization.
 *
 * This function is no-op in non-coverage builds.
 */
#define COVERAGE_ASM_INIT() call coverage_init;

/**
 * Initializes the transport runtime to send coverage report.
 *
 * This function is no-op in non-coverage builds.
 */
#define COVERAGE_ASM_TRANSPORT_INIT() call coverage_transport_init;

/**
 * Backup the first 64 coverage counters from RAM to registers.
 *
 * This function clobbers the a0 register.
 * This function is no-op in non-coverage builds.
 *
 * @param[out] kReg0 A temporary register to store the first 32 counters.
 * @param[out] kReg1 A temporary register to store the next 32 counters.
 */
#define COVERAGE_ASM_BACKUP_COUNTERS(kReg0, kReg1) \
  li a0, 0;                                        \
  call coverage_backup_asm_counters;               \
  mv kReg0, a0;                                    \
  li a0, 32;                                       \
  call coverage_backup_asm_counters;               \
  mv kReg1, a0;

/**
 * Restore the first 64 coverage counters from registers to RAM.
 *
 * This function clobbers the a0 and a1 registers.
 * This function is no-op in non-coverage builds.
 *
 * @param kReg0 A temporary register that stores the first 32 counters.
 * @param kReg1 A temporary register that stores the next 32 counters.
 */
#define COVERAGE_ASM_RESTORE_COUNTERS(kReg0, kReg1) \
  mv a0, kReg0;                                     \
  mv a1, kReg1;                                     \
  call coverage_restore_asm_counters;

/**
 * Triggers a coverage report dump.
 *
 * If the coverage data is valid, it compresses the counter data and sends the
 * report.
 *
 * This function is no-op in non-coverage builds.
 */
#define COVERAGE_ASM_REPORT() call coverage_report;

/**
 * Marks a specific coverage point as hit.
 *
 * This function is no-op in non-coverage builds.
 *
 * @param kTemp A temporary register that will be clobbered.
 * @param kIndex The index of the counter to mark.
 */
#define COVERAGE_ASM_AUTOGEN_MARK(kTemp, kIndex) \
  lui kTemp, % hi(.L__asm_profc + kIndex);       \
  sb zero, % lo(.L__asm_profc + kIndex)(kTemp)

#else  // OT_COVERAGE_INSTRUMENTED

#define COVERAGE_ASM_INIT(...)
#define COVERAGE_ASM_TRANSPORT_INIT(...)
#define COVERAGE_ASM_BACKUP_COUNTERS(...)
#define COVERAGE_ASM_RESTORE_COUNTERS(...)
#define COVERAGE_ASM_REPORT(...)
#define COVERAGE_ASM_AUTOGEN_MARK(...)

#endif  // OT_COVERAGE_INSTRUMENTED

#define COVERAGE_ASM_MANUAL_MARK COVERAGE_ASM_AUTOGEN_MARK

#endif  // OPENTITAN_SW_DEVICE_LIB_COVERAGE_API_ASM_H_
