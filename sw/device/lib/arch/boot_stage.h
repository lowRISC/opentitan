// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_ARCH_BOOT_STAGE_H_
#define OPENTITAN_SW_DEVICE_LIB_ARCH_BOOT_STAGE_H_

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * @file
 * @brief This header contains declarations of boot stage information.
 *
 * This header contains the boot stage specific symbol declarations that can be
 * used by the consumer of this library to determine which stage in the boot
 * sequence the binary is executing from.
 *
 * Definitions for these symbols can be found in other files in this directory,
 * which should be linked in depending on which boot stage an executable is
 * intended for.
 */

/**
 * A `boot_stage_t` represents a particular boot stage.
 */
typedef enum boot_stage {
  /**
   * Undefined boot stage.
   */
  kBootStageNotSet = 0,
  /**
   * The ROM boot stage. Represents the non-mutable code that is used to
   * establish the hardware root of trust in the boot sequence.
   */
  kBootStageRom = 1,
  /**
   * The ROM_EXT boot stage. Represents the first mutable boot stage, which is
   * signed by the Silicon Creator entity.
   */
  kBootStageRomExt = 2,
  /**
   * The First Silicon Owner boot stage.
   */
  kBootStageOwner = 3,
} boot_stage_t;

/**
 * Indicates the boot stage that this program has been linked for.
 *
 * This can be used, for example, for conditioning an operation on the precise
 * boot stage.
 */
extern const boot_stage_t kBootStage;

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_ARCH_BOOT_STAGE_H_
