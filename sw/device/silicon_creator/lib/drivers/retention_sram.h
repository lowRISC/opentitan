// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RETENTION_SRAM_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RETENTION_SRAM_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Retention SRAM silicon creator area.
 */
typedef struct retention_sram_creator {
  /**
   * Reset reasons reported by the reset manager before they were reset in mask
   * ROM.
   */
  uint32_t reset_reasons;
  /**
   * Boot services message area.
   *
   * This is the shared buffer through which ROM_EXT and silicon owner code
   * communicate with each other.
   */
  boot_svc_msg_t boot_svc_msg;

  /**
   * Boot log area.
   *
   * This buffer tracks information about the boot process.
   */
  boot_log_t boot_log;

  /**
   * Shutdown reason.
   *
   * Reason of the last shutdown, redacted according to the redaction policy.
   * This field is initialized to `kErrorOk` on PoR and a value of `kErrorOk`
   * indicates that no shutdowns since the last PoR.
   */
  rom_error_t last_shutdown_reason;
  /**
   * Space reserved for future allocation by the silicon creator.
   *
   * The first half of the retention SRAM is reserved for the silicon creator
   * except for the first word that stores the format version. Hence the total
   * size of this struct must be 2044 bytes. Remaining space is reserved for
   * future use.
   */
  uint32_t reserved[(2044 - sizeof(uint32_t) - sizeof(boot_svc_msg_t) -
                     sizeof(rom_error_t) - sizeof(boot_log_t)) /
                    sizeof(uint32_t)];
} retention_sram_creator_t;
OT_ASSERT_SIZE(retention_sram_creator_t, 2044);

/**
 * Retention SRAM silicon owner area.
 */
typedef struct retention_sram_owner {
  /**
   * Space reserved for allocation by the silicon owner.
   *
   * The silcon creator boot stages will not modify this field except for
   * clearing it at initial power on.
   *
   * Tests that need to trigger (or detect) a device reset may use this field to
   * preserve state information across resets.
   */
  uint32_t reserved[2048 / sizeof(uint32_t)];
} retention_sram_owner_t;
OT_ASSERT_SIZE(retention_sram_owner_t, 2048);

/**
 * The retention SRAM is memory that is used to retain information, such as a
 * boot service request, across a device reset. If the reset reason is 'power
 * on' (POR) all fields will be initialized using the LFSR by the ROM.
 */
typedef struct retention_sram {
  /**
   * Retention SRAM format version.
   *
   * ROM sets this field to `kRetentionSramVersion2` only after PoR and
   * does not modify it otherwise. ROM_EXT can use this information for backward
   * compatibility and set this field to a different value after migrating to a
   * different layout if needed.
   */
  uint32_t version;
  /**
   * Silicon creator area.
   */
  retention_sram_creator_t creator;
  /**
   * Silicon owner area.
   */
  retention_sram_owner_t owner;
} retention_sram_t;

OT_ASSERT_MEMBER_OFFSET(retention_sram_t, creator, 4);
OT_ASSERT_MEMBER_OFFSET(retention_sram_t, owner, 2048);
OT_ASSERT_SIZE(retention_sram_t, 4096);

enum {
  /**
   * Base address of retention SRAM storage area.
   */
  kRetentionSramBase = 0x40600000,
  /**
   * Engineering sample version.
   */
  kRetentionSramVersion1 = 0x72f4eb2e,
  /**
   * Includes the `boot_svc_msg`, `boot_log`, and `last_shutdown_reason` fields
   * in the silicon creator area.
   */
  kRetentionSramVersion2 = 0x5b89bd6d,
};

/**
 * Returns a typed pointer to the retention SRAM.
 *
 * @return A pointer to the retention SRAM.
 */
OT_WARN_UNUSED_RESULT
inline retention_sram_t *retention_sram_get(void) {
  return (retention_sram_t *)kRetentionSramBase;
}

/**
 * Clear the retention SRAM by setting every word to 0.
 */
void retention_sram_clear(void);

/**
 * Initialize the retention SRAM with pseudo-random data from the LFSR.
 *
 * This function does not request a new scrambling key. See
 * `retention_sram_scramble()`.
 *
 * @return Result of the operation.
 */
void retention_sram_init(void);

/**
 * Start scrambling the retention SRAM.
 *
 * Requests a new scrambling key for the retention SRAM. This operation
 * will wipe all of the data in the retention SRAM. The retention SRAM
 * will then be initialized to undefined values.
 *
 * The scrambling operation takes time and accesses to retention SRAM
 * will stall until it completes.
 *
 * @return An error if a new key cannot be requested.
 */
void retention_sram_scramble(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RETENTION_SRAM_H_
