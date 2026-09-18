// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_RV_CORE_IBEX_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_RV_CORE_IBEX_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/status.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Disable the Ibex Instruction Cache if it is enabled.
 *
 * Reads out the current state of the instruction cache. If it is enabled,
 * disable it for the crypto lib.
 *
 * @param[out] icache_enabled kHardenedBoolTrue if the iCache was enabled before
 * we disabled it.
 * @return Error status.
 */
status_t ibex_disable_icache(hardened_bool_t *icache_enabled);

/**
 * Enables the Ibex Instruction Cache if icache_enabled is set.
 *
 * If icache_enabled == kHardenedBoolTrue, this function enables the iCache by
 * writing to CPUCTRL.
 */
void ibex_restore_icache(hardened_bool_t icache_enabled);

/**
 * Checks if the expected Ibex Security Features are enabled.
 *
 * This function reads Ibex cpuctrl register and checks, whether the following
 * security features are enabled:
 * - data_ind_timing
 * - dummy_instr_en
 *
 * @returns Whether the config matches the expected secure config.
 */
OT_WARN_UNUSED_RESULT
hardened_bool_t ibex_check_security_config(void);

/**
 * Enables the expected Ibex Security Features.
 *
 * This function enables the following security features in the Ibex cpuctrl
 * register:
 * - data_ind_timing
 * - dummy_instr_en
 *
 * @returns Error status.
 */
OT_WARN_UNUSED_RESULT
status_t ibex_set_security_config(void);

/**
 * Get random data from the EDN0 interface.
 *
 * Important: this function will hang if the entropy complex is not
 * initialized. Callers are responsible for checking first.
 *
 * @return 32 bits of randomness from EDN0.
 */
uint32_t ibex_rnd32_read(void);

/**
 * Write a random value into x5...x7 and x9...x31.
 *
 * To avoid having SCA sensitive variables in the register file, this function
 * overwrites the RF with a random value.
 * Important:
 * - This function does not overwrite x8/x9 as this might not work with all
 *   compilers. For more information see llvm/llvm-project#157694.
 *   However, ibex_clear_rf() makes sure that x8/x9 is not used for secret
 *   data.
 * - This function will hang if the entropy complex is not initialized.
 *   Callers are responsible for checking first.
 */
static inline __attribute__((always_inline)) void ibex_clear_rf(void) {
#ifdef OT_PLATFORM_RV32
  // ibex_clear_rf() below cannot clear x8 (frame pointer). To avoid that
  // x8 is not used for secret data, create a variable-length array (VLA).
  // This forces the compiler to use x8 instead of the stack pointer,
  // avoiding that x8 can be used for secret data.
  // Similarily, by forcing stack realignment (by having a large alignment),
  // x9 will also be reserved to avoid a similar problem as with x8.
  uint32_t dummy[launderw(0)][4] __attribute__((aligned(32)));
  barrierw((uintptr_t)&dummy);

  // Get random word that gets written into the RF.
  uint32_t rnd = ibex_rnd32_read();
  // Skip x0 ... x4 as those register do not contain sensitive values.
  // x5 ... x7
  asm volatile("lw x5, 0(%0)" : : "r"(&rnd) : "x5");
  asm volatile("lw x6, 0(%0)" : : "r"(&rnd) : "x6");
  asm volatile("lw x7, 0(%0)" : : "r"(&rnd) : "x7");
  // Skip x8/x9 as clobbering this register does not always
  // work, see llvm/llvm-project#157694.
  // x10 ... x31
  asm volatile("lw x10, 0(%0)" : : "r"(&rnd) : "x10");
  asm volatile("lw x11, 0(%0)" : : "r"(&rnd) : "x11");
  asm volatile("lw x12, 0(%0)" : : "r"(&rnd) : "x12");
  asm volatile("lw x13, 0(%0)" : : "r"(&rnd) : "x13");
  asm volatile("lw x14, 0(%0)" : : "r"(&rnd) : "x14");
  asm volatile("lw x15, 0(%0)" : : "r"(&rnd) : "x15");
  asm volatile("lw x16, 0(%0)" : : "r"(&rnd) : "x16");
  asm volatile("lw x17, 0(%0)" : : "r"(&rnd) : "x17");
  asm volatile("lw x18, 0(%0)" : : "r"(&rnd) : "x18");
  asm volatile("lw x19, 0(%0)" : : "r"(&rnd) : "x19");
  asm volatile("lw x20, 0(%0)" : : "r"(&rnd) : "x20");
  asm volatile("lw x21, 0(%0)" : : "r"(&rnd) : "x21");
  asm volatile("lw x22, 0(%0)" : : "r"(&rnd) : "x22");
  asm volatile("lw x23, 0(%0)" : : "r"(&rnd) : "x23");
  asm volatile("lw x24, 0(%0)" : : "r"(&rnd) : "x24");
  asm volatile("lw x25, 0(%0)" : : "r"(&rnd) : "x25");
  asm volatile("lw x26, 0(%0)" : : "r"(&rnd) : "x26");
  asm volatile("lw x27, 0(%0)" : : "r"(&rnd) : "x27");
  asm volatile("lw x28, 0(%0)" : : "r"(&rnd) : "x28");
  asm volatile("lw x29, 0(%0)" : : "r"(&rnd) : "x29");
  asm volatile("lw x30, 0(%0)" : : "r"(&rnd) : "x30");
  asm volatile("lw x31, 0(%0)" : : "r"(&rnd) : "x31");
#else  // OT_PLATFORM_RV32
  asm volatile("nop");
#endif
}

#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_RV_CORE_IBEX_H_
